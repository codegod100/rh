/-
  Peano Arithmetic Language and Theory (Scaffold)

  This file defines a minimal first-order language for PA. The axiom
  set is currently a placeholder and should be expanded to full PA.
-/

import Mathlib.ModelTheory.Syntax

open FirstOrder
open scoped FirstOrder
open Language

inductive PA_FunTag
  | zero
  | succ
  | add
  | mul

def PA_FunTag.arity : PA_FunTag → Nat
  | .zero => 0
  | .succ => 1
  | .add => 2
  | .mul => 2

inductive PA_RelTag
  | le

def PA_RelTag.arity : PA_RelTag → Nat
  | .le => 2

def PA_Lang : Language :=
  { Functions := fun n => { t : PA_FunTag // PA_FunTag.arity t = n }
  , Relations := fun n => { t : PA_RelTag // PA_RelTag.arity t = n } }

def pa_zero_sym : PA_Lang.Functions 0 :=
  ⟨PA_FunTag.zero, rfl⟩

def pa_succ_sym : PA_Lang.Functions 1 :=
  ⟨PA_FunTag.succ, rfl⟩

def pa_add_sym : PA_Lang.Functions 2 :=
  ⟨PA_FunTag.add, rfl⟩

def pa_mul_sym : PA_Lang.Functions 2 :=
  ⟨PA_FunTag.mul, rfl⟩

def zeroTerm {α : Type*} : PA_Lang.Term α :=
  Term.func pa_zero_sym (fun i => Fin.elim0 i)

def succTerm {α : Type*} (t : PA_Lang.Term α) : PA_Lang.Term α :=
  Language.Functions.apply₁ pa_succ_sym t

def addTerm {α : Type*} (t₁ t₂ : PA_Lang.Term α) : PA_Lang.Term α :=
  Language.Functions.apply₂ pa_add_sym t₁ t₂

def mulTerm {α : Type*} (t₁ t₂ : PA_Lang.Term α) : PA_Lang.Term α :=
  Language.Functions.apply₂ pa_mul_sym t₁ t₂

def pa_zero_ne_succ : PA_Lang.Sentence :=
  BoundedFormula.all ((Term.bdEqual (succTerm (&0)) (zeroTerm)).not)

def pa_succ_injective : PA_Lang.Sentence :=
  BoundedFormula.all <|
    BoundedFormula.all <|
      BoundedFormula.imp
        (Term.bdEqual (succTerm (&0)) (succTerm (&1)))
        (Term.bdEqual (&0) (&1))

def pa_add_zero : PA_Lang.Sentence :=
  BoundedFormula.all <|
    Term.bdEqual (addTerm (&0) (zeroTerm)) (&0)

def pa_add_succ : PA_Lang.Sentence :=
  BoundedFormula.all <|
    BoundedFormula.all <|
      Term.bdEqual (addTerm (&0) (succTerm (&1))) (succTerm (addTerm (&0) (&1)))

def pa_mul_zero : PA_Lang.Sentence :=
  BoundedFormula.all <|
    Term.bdEqual (mulTerm (&0) (zeroTerm)) (zeroTerm)

def pa_mul_succ : PA_Lang.Sentence :=
  BoundedFormula.all <|
    BoundedFormula.all <|
      Term.bdEqual (mulTerm (&0) (succTerm (&1))) (addTerm (mulTerm (&0) (&1)) (&0))

def pa_induction (φ : PA_Lang.Formula (Fin 1)) : PA_Lang.Sentence :=
  let φ_zero : PA_Lang.Sentence :=
    BoundedFormula.subst φ (fun _ => (zeroTerm (α := Empty)))
  let relabelToBound : Fin 1 → Empty ⊕ Fin 1 :=
    fun _ => Sum.inr 0
  let φ_var : PA_Lang.BoundedFormula Empty 1 :=
    BoundedFormula.relabel relabelToBound φ
  let φ_succ : PA_Lang.BoundedFormula Empty 1 :=
    BoundedFormula.relabel relabelToBound <|
      BoundedFormula.subst φ (fun _ => succTerm (Term.var (0 : Fin 1)))
  let step : PA_Lang.Sentence :=
    BoundedFormula.all (BoundedFormula.imp φ_var φ_succ)
  let concl : PA_Lang.Sentence :=
    BoundedFormula.all φ_var
  BoundedFormula.imp (φ_zero ⊓ step) concl

def pa_induction_schema : Set PA_Lang.Sentence :=
  Set.range pa_induction

def PA_Theory : PA_Lang.Theory :=
  ({pa_zero_ne_succ, pa_succ_injective, pa_add_zero, pa_add_succ,
    pa_mul_zero, pa_mul_succ} : Set PA_Lang.Sentence) ∪ pa_induction_schema
