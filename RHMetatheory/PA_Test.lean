/-
  PA Axiom Tests (TDD)

  These examples define the expected concrete axiom sentences.
  They should be definitionally equal to the definitions in PA.lean.
-/

import RHMetatheory.PA

open FirstOrder
open scoped FirstOrder

def expected_zero_ne_succ : PA_Lang.Sentence :=
  BoundedFormula.all ((Term.bdEqual (succTerm (&0)) (zeroTerm)).not)

def expected_succ_injective : PA_Lang.Sentence :=
  BoundedFormula.all <|
    BoundedFormula.all <|
      BoundedFormula.imp
        (Term.bdEqual (succTerm (&0)) (succTerm (&1)))
        (Term.bdEqual (&0) (&1))

def expected_add_zero : PA_Lang.Sentence :=
  BoundedFormula.all <|
    Term.bdEqual (addTerm (&0) (zeroTerm)) (&0)

def expected_add_succ : PA_Lang.Sentence :=
  BoundedFormula.all <|
    BoundedFormula.all <|
      Term.bdEqual (addTerm (&0) (succTerm (&1))) (succTerm (addTerm (&0) (&1)))

def expected_mul_zero : PA_Lang.Sentence :=
  BoundedFormula.all <|
    Term.bdEqual (mulTerm (&0) (zeroTerm)) (zeroTerm)

def expected_mul_succ : PA_Lang.Sentence :=
  BoundedFormula.all <|
    BoundedFormula.all <|
      Term.bdEqual (mulTerm (&0) (succTerm (&1))) (addTerm (mulTerm (&0) (&1)) (&0))

example : pa_zero_ne_succ = expected_zero_ne_succ := rfl
example : pa_succ_injective = expected_succ_injective := rfl
example : pa_add_zero = expected_add_zero := rfl
example : pa_add_succ = expected_add_succ := rfl
example : pa_mul_zero = expected_mul_zero := rfl
example : pa_mul_succ = expected_mul_succ := rfl
