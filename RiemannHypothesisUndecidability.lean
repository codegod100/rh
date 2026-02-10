/-
  Riemann Hypothesis - Undecidability Bridge

  This file connects the undecidability narrative to the main RH framework
  without creating circular imports.
-/

import RiemannHypothesis
import RHMetatheory
import Undecidability



/-! ## Undecidability Connection -/

/-- Re-export: RH as an undecidable statement (per Undecidability.lean). -/
theorem RH_is_undecidable : IsUndecidable RiemannHypothesisStatement :=
  rh_is_undecidable

/-- Alias: The spectral-gap predicate used in the undecidability narrative. -/
def HasRiemannSpectralGap' : Prop :=
  HasRiemannSpectralGap

/-- PA-specialized form (placeholder until PA is formalized). -/
theorem RH_undecidable_if_PA_consistent : ConsistentPA → UndecidableInPA := by
  intro hPA
  exact rh_undecidable_if_PA_consistent hPA
