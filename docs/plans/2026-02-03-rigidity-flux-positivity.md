# Rigidity Implies Flux Positivity Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace the `sorry` in `rigidity_implies_flux_positivity` with a structured proof that composes explicit analytic bounds implied by spectral rigidity.

**Architecture:** Decompose the proof into three analytic lemmas (Gamma flux upper bound, zero-gap/density from rigidity, and flux lower bound from a nearby zero), then combine them in a comparison lemma that yields positivity of `BhairavaFlux`. Keep the composition proof in Lean; isolate external analytic number theory in clearly named lemmas (initially axioms if needed).

**Tech Stack:** Lean4 + Mathlib, `lake build`

---

### Task 1: Add explicit analytic lemma statements near the theorem

**Files:**
- Modify: `RiemannHypothesis.lean`

**Step 1: Add lemma statements (placeholders) close to `rigidity_implies_flux_positivity`**

```lean
axiom gamma_flux_upper_bound :
  ∃ C_g, ∀ (τ : ℝ), τ > 10 → abs (GammaFluxContribution ((σ : ℂ) + (τ : ℂ) * I)) < C_g / τ^2

axiom rigidity_gives_nearby_zero :
  (∀ α, PrimePairCorrelation α = if |α| < 1 then |α| else 1) →
  ∀ t > 10, ∃ γ : ℝ, IsZetaZero ((0.5 : ℂ) + (γ : ℂ) * I) ∧ |t - γ| < C_z / Real.log (|t| + 2)

axiom flux_contribution_lower_bound :
  ∀ γ : ℝ, IsZetaZero ((0.5 : ℂ) + (γ : ℂ) * I) →
  FluxContribution ((σ : ℂ) + (t : ℂ) * I) ((0.5 : ℂ) + (γ : ℂ) * I) > (1 : ℝ) / (t - γ)^2
```

**Step 2: Run build to ensure no syntax errors**

Run: `lake build`
Expected: Build succeeds (axioms may generate warnings only).

### Task 2: Prove the comparison lemma that combines bounds into a positive flux

**Files:**
- Modify: `RiemannHypothesis.lean`

**Step 1: Add a local lemma (no new axioms) that compares lower and upper bounds**

```lean
lemma flux_positive_of_bounds
  (t σ : ℝ)
  (h_strip : σ ∈ Set.Icc 0 1)
  (h_gamma : abs (GammaFluxContribution ((σ : ℂ) + (t : ℂ) * I)) < C_g / t^2)
  (h_zero : ∃ γ : ℝ, IsZetaZero ((0.5 : ℂ) + (γ : ℂ) * I) ∧ |t - γ| < C_z / Real.log (|t| + 2))
  (h_flux : ∀ γ, IsZetaZero ((0.5 : ℂ) + (γ : ℂ) * I) →
    FluxContribution ((σ : ℂ) + (t : ℂ) * I) ((0.5 : ℂ) + (γ : ℂ) * I) > (1 : ℝ) / (t - γ)^2) :
  BhairavaFlux t σ > 0 := by
  -- combine the nearby-zero lower bound with the gamma upper bound
  sorry
```

**Step 2: Run build to confirm it compiles**

Run: `lake build`
Expected: Build succeeds (with one `sorry`).

### Task 3: Rewire `rigidity_implies_flux_positivity` to use the new lemmas

**Files:**
- Modify: `RiemannHypothesis.lean`

**Step 1: Replace the current proof sketch with the composed lemma**

```lean
theorem rigidity_implies_flux_positivity :
  (∀ α, PrimePairCorrelation α = if |α| < 1 then |α| else 1) →
  (∀ t σ, σ ∈ Set.Icc 0 1 → BhairavaFlux t σ > 0) := by
  intro h_rigid t σ h_strip
  obtain ⟨C_g, h_gamma⟩ := gamma_flux_upper_bound
  have h_zero := rigidity_gives_nearby_zero h_rigid t (by linarith)
  have h_flux := flux_contribution_lower_bound
  -- finish with flux_positive_of_bounds
  sorry
```

**Step 2: Run build**

Run: `lake build`
Expected: Build succeeds (with remaining `sorry`s only in the new lemmas, if any).

### Task 4: Optional tightening (remove axioms one by one)

**Files:**
- Modify: `RiemannHypothesis.lean`

**Step 1: Replace `axiom` placeholders with lemma statements + `by` proofs**

Start with the simplest analytic claim you can formalize in Mathlib (likely an inequality manipulation lemma). Leave the heavy analytic number theory claims as axioms.

**Step 2: Run build**

Run: `lake build`
Expected: Build succeeds with fewer axioms.
