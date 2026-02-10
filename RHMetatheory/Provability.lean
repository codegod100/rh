/-
  Provability Layer (Placeholder)

  This file introduces a minimal provability predicate for theories.
  Replace with a syntactic derivability relation when available.
-/

import Mathlib.ModelTheory.Syntax

open FirstOrder

def ProvableIn {L : Language} (T : L.Theory) (φ : L.Sentence) : Prop :=
  False

def UndecidableSentenceIn {L : Language} (T : L.Theory) (φ : L.Sentence) : Prop :=
  ¬ ProvableIn T φ ∧ ¬ ProvableIn T φ.not
