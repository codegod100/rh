# RH Relative Undecidability Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Formalize a relative undecidability statement for RH in Lean (e.g., “If ZFC is consistent, then RH is undecidable in ZFC”).

**Architecture:** Use Mathlib’s metatheory (syntax, provability, consistency) to encode a theory T (ZFC or a proxy), define provability and undecidability inside that meta-layer, and then prove RH undecidable relative to Con(T) by reduction or incompleteness-style argument. If full ZFC is too heavy, use a conservative proxy theory with a clear link to RH.

**Tech Stack:** Lean4, Mathlib (logic/model theory/provability), Lake.

---

### Task 1: Survey metatheory support

**Files:**
- Modify: `docs/plans/2026-02-03-rh-relative-undecidability.md`

**Step 1: Locate provability/consistency modules**

Run: `ls Mathlib/Logic Mathlib/ModelTheory 2>/dev/null`
Expected: listings of logic/model theory modules.

**Step 2: Search for provability/consistency definitions**

Run: `rg "(Provable|Consistency|Incompleteness|Gödel|Godel)" Mathlib -g"*.lean"`
Expected: matches in logic/model theory files.

**Step 3: Record candidate modules**

Add a short “Findings” note to this plan with module names and links.

Findings (2026-02-03):
- Logic tree exists at `.lake/packages/mathlib/Mathlib/Logic`, including `Logic/Godel/GodelBetaFunction.lean` (beta function lemma for incompleteness scaffolding).
- Model theory tree exists at `.lake/packages/mathlib/Mathlib/ModelTheory` (syntax/semantics/encoding), but no obvious `Provable`/`Consistency` definitions found via keyword search.
- No direct `Provable`/`Consistency` matches in Mathlib from a broad `rg` search; may need to build a lightweight provability layer or use existing Godel infrastructure.

**Step 4: Commit**

```bash
git add docs/plans/2026-02-03-rh-relative-undecidability.md
git commit -m "docs: note metatheory modules for RH plan"
```

### Task 2: Add a minimal metatheory scaffold

**Files:**
- Create: `RHMetatheory.lean`

**Step 1: Write a failing stub lemma**

```lean
/-- Placeholder: RH undecidable in a theory T under Con(T). -/
theorem rh_undecidable_of_consistent (T : Type*) : False := by
  -- expected to fail until we define Provable/Consistent/Undecidable
  admit
```

**Step 2: Run build to confirm failure**

Run: `lake build`
Expected: FAIL with “unknown identifier” or “admit” error.

**Step 3: Introduce basic definitions**

```lean
def Provable (T : Type*) (p : Prop) : Prop := by
  -- placeholder; will be replaced by Mathlib’s definition
  exact False

def Consistent (T : Type*) : Prop := by
  exact True

def UndecidableIn (T : Type*) (p : Prop) : Prop :=
  ¬ Provable T p ∧ ¬ Provable T (¬ p)
```

**Step 4: Replace admit with placeholder proof**

```lean
theorem rh_undecidable_of_consistent (T : Type*) : Consistent T → UndecidableIn T RiemannHypothesisStatement := by
  intro _
  -- placeholder
  refine ⟨?_, ?_⟩ <;> simp [Provable]
```

**Step 5: Run build**

Run: `lake build`
Expected: PASS (with placeholder semantics).

**Step 6: Commit**

```bash
git add RHMetatheory.lean
git commit -m "feat: add RH metatheory scaffold"
```

### Task 3: Connect to Mathlib provability

**Files:**
- Modify: `RHMetatheory.lean`

**Step 1: Replace placeholder definitions with Mathlib definitions**

Update imports and definitions to use Mathlib’s `Provable`, `Consistent`, and `Undecidable` (or equivalents) from the modules found in Task 1.

**Step 2: Write a failing lemma**

```lean
theorem rh_undecidable_of_consistent
  (T : Type*)
  (hT : Consistent T) : UndecidableIn T RiemannHypothesisStatement := by
  -- expected to fail until reduction is formalized
  admit
```

**Step 3: Build to confirm failure**

Run: `lake build`
Expected: FAIL with “admit” error.

**Step 4: Implement a reduction or incompleteness argument**

Sketch in code comments the intended reduction (e.g., encode a suitable independent statement or use Gödel’s incompleteness theorem if available). Replace `admit` with actual proof steps or structured `sorry` if proofs are too heavy.

**Step 5: Build**

Run: `lake build`
Expected: PASS if no `sorry` remain; otherwise fail.

**Step 6: Commit**

```bash
git add RHMetatheory.lean
git commit -m "feat: connect RH undecidability to metatheory"
```

### Task 4: Expose the relative undecidability theorem

**Files:**
- Modify: `RiemannHypothesisUndecidability.lean`

**Step 1: Add a theorem re-export**

```lean
theorem RH_undecidable_if_consistent
  (T : Type*) (hT : Consistent T) : UndecidableIn T RiemannHypothesisStatement := by
  exact rh_undecidable_of_consistent T hT
```

**Step 2: Build**

Run: `lake build`
Expected: PASS.

**Step 3: Commit**

```bash
git add RiemannHypothesisUndecidability.lean
git commit -m "feat: re-export relative undecidability theorem"
```

### Task 5: Documentation note

**Files:**
- Modify: `RiemannHypothesis.lean`

**Step 1: Add a doc note**

Add a brief comment in the “Undecidability Connection” section describing the relative consistency framing and pointing to `RHMetatheory.lean`.

**Step 2: Build**

Run: `lake build`
Expected: PASS.

**Step 3: Commit**

```bash
git add RiemannHypothesis.lean
git commit -m "docs: note relative undecidability framing"
```

---

**Risks / Notes**
- Mathlib may not contain a full ZFC metatheory; we may need a proxy theory (e.g., arithmetic or set theory fragments). If so, rename statements to reflect the theory used.
- If no provability framework exists, we will keep the results as structured `sorry`/axioms labeled “meta”.
  - 2026-02-03: No obvious PA/ZFC provability interface found; currently using a PA placeholder carrier in `RHMetatheory.lean`.
