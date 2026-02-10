# PA Metatheory for RH Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace the placeholder PA layer with a real First-Order PA theory and a provability predicate sufficient to state “Con(PA) → UndecidableIn PA RH.”

**Architecture:** Use Mathlib’s First-Order logic (`ModelTheory/Syntax`, `Semantics`, `Satisfiability`) to define a PA language, axioms as a `Theory`, and a provability predicate from derivability. If Mathlib lacks incompleteness, keep the final undecidability lemma as a structured `sorry` labeled “meta” while keeping all definitions concrete.

**Tech Stack:** Lean4, Mathlib ModelTheory (Syntax/Semantics), Lake.

---

### Task 1: Identify existing provability/derivability APIs

**Files:**
- Modify: `docs/plans/2026-02-03-pa-metatheory.md`

**Step 1: Search for Theory/Proves/Derivable**

Run: `rg "(Theory|Proves|Derivable|Deduction|Sequent)" .lake/packages/mathlib/Mathlib/ModelTheory -g"*.lean"`
Expected: matches in `Syntax`, `Semantics`, or `Satisfiability`.

**Step 2: Record findings**

Add a short “Findings” note with module names and key identifiers.

Findings (2026-02-03):
- `Mathlib/ModelTheory/Syntax.lean` defines `FirstOrder.Language.Theory` (as a set of sentences).
- `Mathlib/ModelTheory/Semantics.lean` defines `Theory.Model` and `T ⊨ φ` semantics.
- `Mathlib/ModelTheory/Equivalence.lean` defines `Theory.Imp` / `Theory.Iff` for semantic implication.
- No obvious proof system (`Proves`/`Derivable`) found in ModelTheory; likely need placeholders or custom derivability.
- Arithmetic-specific directory exists at `Mathlib/ModelTheory/Arithmetic/Presburger`, but not a full PA development.

**Step 3: Commit**

```bash
git add docs/plans/2026-02-03-pa-metatheory.md
git commit -m "docs: note PA metatheory entry points"
```

### Task 2: Define the PA language and axioms

**Files:**
- Create: `RHMetatheory/PA.lean`

**Step 1: Write a failing stub to check imports**

```lean
import Mathlib.ModelTheory.Syntax

-- expected to fail until Language imported/used
#check FirstOrder.Language
```

**Step 2: Run build to confirm baseline**

Run: `lake build`
Expected: PASS (or FAIL with missing imports).

**Step 3: Define PA language**

```lean
open FirstOrder

def PA_Lang : Language :=
{ Functions := fun n =>
    match n with
    | 0 => PUnit     -- 0-ary: zero constant
    | 1 => PUnit     -- 1-ary: succ
    | 2 => Bool      -- 2-ary: add/mul
    | _ => PEmpty
  , Relations := fun n =>
    match n with
    | 2 => PUnit     -- 2-ary: equality or less-than (choose one)
    | _ => PEmpty }
```

**Step 4: Encode constants/functions by named tags**

```lean
inductive PA_FunTag | zero | succ | add | mul
inductive PA_RelTag | le

-- map tags to arities and define Language with tags
```

**Step 5: Define PA axioms as a `Theory`**

Create sentences for zero/succ injective, induction schema (as an axiom set), and arithmetic recursion as needed for your target strength.

**Step 6: Run build**

Run: `lake build`
Expected: PASS.

**Step 7: Commit**

```bash
git add RHMetatheory/PA.lean
git commit -m "feat: define PA language and axioms"
```

### Task 3: Define provability and consistency for PA

**Files:**
- Create: `RHMetatheory/Provability.lean`
- Modify: `RHMetatheory.lean`

**Step 1: Create a failing stub**

```lean
import RHMetatheory.PA

def PA_Theory : FirstOrder.Theory PA_Lang := by
  -- expected to fail until Theory imported/defined
  admit
```

**Step 2: Run build to confirm failure**

Run: `lake build`
Expected: FAIL at `admit`.

**Step 3: Implement PA_Theory and ProvableIn**

Use Mathlib’s `Theory` + derivability predicates if present (from Task 1). If not found, define a minimal placeholder `ProvableIn` with TODOs.

**Step 4: Define consistency**

```lean
def ConsistentPA : Prop :=
  ¬ (ProvableIn PA_Theory ⊥)
```

**Step 5: Wire into `RHMetatheory.lean`**

Replace placeholder `PA`/`ConsistentPA`/`UndecidableIn` with these definitions.

**Step 6: Build**

Run: `lake build`
Expected: PASS (or known failures from existing files).

**Step 7: Commit**

```bash
git add RHMetatheory/Provability.lean RHMetatheory.lean
git commit -m "feat: add PA provability/consistency layer"
```

### Task 4: State relative undecidability over PA

**Files:**
- Modify: `RiemannHypothesisUndecidability.lean`

**Step 1: Add theorem statement**

```lean
theorem RH_undecidable_in_PA_of_consistent :
  ConsistentPA → UndecidableIn PA_Theory RiemannHypothesisStatement := by
  -- If Mathlib incompleteness is missing, leave a labeled `sorry` with a docstring.
  sorry
```

**Step 2: Build**

Run: `lake build`
Expected: FAIL if `sorry` disallowed, otherwise PASS.

**Step 3: Commit**

```bash
git add RiemannHypothesisUndecidability.lean
git commit -m "feat: state RH undecidability relative to PA"
```

### Task 5: Documentation note

**Files:**
- Modify: `RiemannHypothesis.lean`

**Step 1: Add a doc note**

Briefly mention the PA formalization location (`RHMetatheory/PA.lean`) and that the undecidability proof is conditional on an incompleteness theorem formalization.

**Step 2: Build**

Run: `lake build`
Expected: PASS (or known repo failures).

**Step 3: Commit**

```bash
git add RiemannHypothesis.lean
git commit -m "docs: note PA metatheory location"
```

---

**Risks / Notes**
- PA is not obviously defined in Mathlib; we may need to define the language and axiom schema ourselves.
- Full incompleteness may not be present; keep the final undecidability lemma as a labeled `sorry` if needed.
