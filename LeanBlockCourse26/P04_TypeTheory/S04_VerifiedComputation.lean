/-
# Verified Computation and Trust
=====================

The payoff: verified computation with Subtype, axiom tracing with
`#print axioms`, and the trust model.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Cases

open Nat

/-
## Type classes and instances

### Inhabited
-/

#check Inhabited
#check @instInhabitedNat

#eval @Inhabited.default Nat _

-- `Inhabited α` lives in `Type`: we can compute with the default element.

/-
### Nonempty
-/

#check Nonempty

#check Nonempty.intro Nat

-- `Nonempty α` lives in `Prop`, so we cannot evaluate it for runtime data.
-- #eval Nonempty.intro Nat

-- A proposition is nonempty if we already have a term `p : P`.
variable (P : Prop) (p : P)
example : Nonempty P := Nonempty.intro p

-- Still not evaluatable: `Prop` carries no runtime data.
-- #eval Nonempty.intro Nat
#check Nonempty.intro P

/-
### Decidable and DecidablePred
-/

#check Decidable
#check DecidablePred

#check @instDecidableAnd

def p_nat_even := (fun n : Nat => n % 2 = 0)

noncomputable instance pNatEvenDecidableClassical : DecidablePred p_nat_even :=
  Classical.decPred p_nat_even


-- instance pNatEvenDecidableConstructive : DecidablePred p_nat_even :=
  -- intro n
  -- | isFalse => sorry
  -- | isTrue => sorry

/-
## Verified computation

The pattern:
1. Write an algorithm with a plain type signature.
2. Prove a property as a separate theorem.
3. Bundle into Subtype — the return type carries the guarantee.
-/

section VerifiedFilter

variable {α : Type}

-- Step 1: algorithm. `[DecidablePred p]` lets `if` branch on a Prop.

/-
`List` is defined inductively in Lean with constructors for an empty
list (`nil`) and a constructor `cons` that prepends an element
`(head : α)` to a given existing list `(tail : List α)`.

inductive List (α : Type u) where
  | nil : List α 
  | cons (head : α) (tail : List α) : List α

Bracket notation uses `[] = List.nil`.
-/

def propFilter (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => []
  | head :: tail =>
      let filtered_tail := propFilter p tail
      if (p head) then
        head :: filtered_tail
      else
        filtered_tail

-- This evaluates computationally.
#eval propFilter (fun n : Nat => n % 2 = 0) [1, 2, 3, 4, 5, 6]


-- This fails when the decision procedure is noncomputable:

-- depends on `Classical.choice`.
-- #eval propFilter p_nat_even [1, 2, 3, 4, 5, 6]

-- Exercise: prove that `propFilter` is sound
-- Step 2a: prove soundness — everything in the output satisfies p.
theorem propFilter_sound (p : α → Prop) [DecidablePred p] (xs : List α) :
    ∀ x ∈ propFilter p xs, p x := by
  intro x hx
  induction xs with
  | nil =>
     unfold propFilter at hx  -- shown explicitly for pedagogy
     exfalso
     exact (List.mem_nil_iff x).mp hx
  | cons y ys ih => 
     unfold propFilter at hx
     split at hx
     case isTrue h =>
      cases hx with
       | head => exact h
       | tail _ hmem => exact ih hmem
     case isFalse h =>
      exact ih hx

theorem propFilter_sound' (p : α → Prop) [DecidablePred p] (xs : List α) :
    ∀ x ∈ propFilter p xs, p x := by
  intro x hx
  induction xs
  · contradiction
  next y ys ih =>
    by_cases h : p y
    · rw [show propFilter p (y :: ys) = y :: propFilter p ys from if_pos h] at hx
      obtain _ | ⟨_, hmem⟩ := hx
      · exact h
      · exact ih hmem
    · rw [show propFilter p (y :: ys) = propFilter p ys from if_neg h] at hx
      exact ih hx

#print axioms propFilter_sound'

-- Step 2b: prove completeness — everything in `xs` but not in the output does not satisfy `p`.
theorem propFilter_complete (p : α → Prop) [DecidablePred p] (xs : List α) :
    ∀ x, x ∈ xs ∧ x ∉ propFilter p xs → ¬ p x := by
  intro x ⟨x_in_xs, hx⟩ px
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
      unfold propFilter at hx
      split at hx
      case isTrue h =>
        cases x_in_xs with
        | head => exact hx List.mem_cons_self
        | tail _ hmem => exact ih hmem (fun h' => hx (.tail _ h'))
      case isFalse h =>
        cases x_in_xs with
        | head => exact h px
        | tail _ hmem => exact ih hmem hx

theorem propFilter_complete' (p : α → Prop) [DecidablePred p] (xs : List α) :
    ∀ x, x ∈ xs ∧ x ∉ propFilter p xs → ¬ p x := by
  intro x ⟨x_in_xs, hx⟩ px
  induction xs
  · contradiction
  next y ys ih =>
    by_cases h : p y
    · rw [show propFilter p (y :: ys) = y :: propFilter p ys from if_pos h] at hx
      obtain _ | ⟨_, hmem⟩ := x_in_xs
      · exact hx List.mem_cons_self
      · exact ih hmem (fun h' => hx (List.mem_cons_of_mem _ h'))
    · rw [show propFilter p (y :: ys) = propFilter p ys from if_neg h] at hx
      obtain _ | ⟨_, hmem⟩ := x_in_xs
      · exact h px
      · exact ih hmem hx

-- Step 3: bundle algorithm + proof into Subtype.
-- Note: we cannot state `∀ x, (x ∈ ys ∧ p x) ∨ (x ∉ ys ∧ ¬ p x)` because
-- for `x ∉ xs` we have `x ∉ ys` but cannot conclude `¬ p x`.
def verifiedFilter (p : α → Prop) [DecidablePred p] (xs : List α) :
    { ys : List α // (∀ x ∈ ys, p x) ∧ (∀ x, x ∈ xs ∧ x ∉ ys → ¬ p x) } :=
  ⟨propFilter p xs, propFilter_sound p xs, propFilter_complete p xs⟩

#eval (verifiedFilter (fun n : Nat => n % 2 = 0) [1, 2, 3, 4, 5, 6]).val

end VerifiedFilter


-- We can turn the P01S04 infinitude-of-primes proof into a verified algorithm.
def exists_infinite_primes_algorithm (n : ℕ) :
    { p : ℕ // n ≤ p ∧ Nat.Prime p } :=
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := Nat.ne_of_gt <| succ_lt_succ <| factorial_pos _
  have pp : Nat.Prime p := minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, np, pp⟩

-- This computes a concrete prime.
#eval exists_infinite_primes_algorithm 4

-- It still depends on classical axioms.
#print axioms exists_infinite_primes_algorithm

-- In particular through the `minFac` stack:
#print axioms minFac        -- [propext, Classical.choice, Quot.sound]
#print axioms minFacAux     -- [propext, Classical.choice, Quot.sound]

/-
`minFacAux` still reports axioms in this toolchain. This highlights that
`#print axioms` tracks declaration-level logical dependencies, not only
runtime behavior after proof erasure.

Unlike our subtype example, `minFac` does not bundle
the (to us) relevant property that the output is prime. Instead
we had to invoke `minFac_prime`.
-/

-- Downstream lemmas inherit these dependencies.
#print axioms minFac_prime  -- [propext, Classical.choice, Quot.sound]
#print axioms minFac_dvd    -- [propext, Classical.choice, Quot.sound]
#print axioms minFac_pos    -- [propext, Classical.choice, Quot.sound]

#print axioms dvd_factorial         -- propext
#print axioms Nat.dvd_add_iff_right -- propext


/-
Any axiom is just a `theorem` without a proof or a `def` without an
implementation. It satisfies the typechecker, but does not produce
computable code.

```
axiom myChoice (P : Prop) : P ∨ ¬ P
```

But we need to be careful with this, because as soon as we define
a contradiction, everything collapses:

```
axiom myFallacy : False

theorem weHaveAProblem : 2 = 3 := by
  exfalso
  exact myFallacy
```
-/

#check False

namespace DangerousExample
axiom myAxiom : ∀ (Q : Prop), Q
theorem oops : False := myAxiom False
end DangerousExample

-- `sorry` introduces the axiom `sorryAx`:
#check @sorryAx

-- Lean's three mathematical axioms:
#check @propext
#check @Quot.sound
#check @Classical.choice

-- Derived principles:
#check @funext
#print axioms funext
#check @Classical.em
#print axioms Classical.em

-- `False.elim` is constructive (no axioms).
#print axioms False.elim

-- Compilation trust axioms (for executable code paths):
#check @Lean.ofReduceBool
#check @Lean.ofReduceNat
#check @Lean.trustCompiler
