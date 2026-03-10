/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Use
import Mathlib.Tactic.ByContra

/-
# Defining the Natural Numbers
=====================

## The inductive definition of `MyNat`
-/

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

#check MyNat.noConfusion


namespace MyNat

instance myNatInhabited : Inhabited MyNat where
  default := MyNat.zero -- Would also be valid to use `MyNat.zero.succ.succ`

#eval myNatInhabited.default -- tells us our default instance of `MyNat` is `MyNat.zero`

#check 0 -- Note that this is still `Nat` and `(0 : MyNat)` coercion fails

-- Establish a coercion method from `Nat` to `MyNat` so we can use numerals
def ofNat (x : Nat) : MyNat :=
  match x with
  | Nat.zero => MyNat.zero
  | Nat.succ b => MyNat.succ (ofNat b)

#eval ofNat 0
#eval ofNat 1

instance instOfNat {n : Nat} : OfNat MyNat n where
  ofNat := ofNat n

#check (0 : MyNat) -- manually coerces `0` into MyNat.zero

def foo (n : MyNat) : MyNat := n

#check foo 1 -- coercion turns `1` into `1 : MyNat`

-- Some basic theorems about successors in MyNat
theorem one_eq_succ_zero : 1 = succ 0 := rfl
theorem two_eq_succ_one : 2 = succ 1 := rfl
theorem three_eq_succ_two : 3 = succ 2 := rfl
theorem four_eq_succ_three : 4 = succ 3 := rfl
theorem five_eq_succ_four : 5 = succ 4 := rfl
theorem zero_eq_zero : 0 = zero := rfl

/-
## Exercise Block B01
-/

-- Exercise 1.1
example : 2 = succ (succ 0) := by
  rw [two_eq_succ_one, one_eq_succ_zero]

example : 2 = succ (succ 0) := by
  rw [← one_eq_succ_zero, ← two_eq_succ_one]

example : 2 = succ (succ 0) := rfl

-- Exercise 1.2
theorem eq_succ_of_ne_zero {n : MyNat} (h : n ≠ 0) :
    ∃ m : MyNat, n = succ m := by
  -- Hint: try `induction n` or just `cases n`
  cases n with
  | zero => contradiction
  | succ k => use k

-- Exercise 1.3 (Master)
-- Turn Exercise 1.2 into a verified algorithm
def eq_succ_of_ne_zero_algorithm {n : MyNat} (h : n ≠ 0) :
    { m : MyNat // n = succ m } := by
  cases n with
  | zero => contradiction
  | succ k => use k

/-
## Peano Axioms

In introductory math courses you will usually see natural numbers
defined through a set of Peano axioms, which assume we are given
"a constant symbol `0` and a unary function symbol `S`", which for
us are `MyNat.zero` (constant constructor) and `MyNat.succ` (dependent
constructor):

1. 0 is a natural number.
   ⟩ Taken care of with `MyNat.zero`, meaning it is nonsensical
     (not part of `Prop` world) or trivial (`#check MyNat.zero`
     confirms type on a meta level) in (D)TT in Lean ✔

2. For every natural number x, x = x. That is, equality is reflexive.
   ⟩ Taken care of through `Eq.rfl` ✔

3. For all natural numbers x and y, if x = y, then y = x. That is,
   equality is symmetric.
   ⟩ Taken care of through `Eq.symm` ✔

4. For all natural numbers x, y and z, if x = y and y = z, then
   x = z. That is, equality is transitive.
   ⟩ Taken care of through `Eq.mp`, `congrArg`, and functional types ✔

5. For all a and b, if b is a natural number and a = b, then a is
   also a natural number. That is, the natural numbers are closed
   under equality.
   ⟩ Either nonsensical or trivially true in (D)TT in Lean, see (1) ✔

6. For every natural number n, S(n) is a natural number. That is,
   the natural numbers are closed under S.
   ⟩ Taken care of with `MyNat.succ`, see (1) ✔

7. For all natural numbers m and n, if S(m) = S(n), then m = n.
   That is, S is an injection.
   ⟩ Taken care of by the Lean kernel giving us `MyNat.noConfusion` ✔

8. For every natural number n, S(n) = 0 is false. That is, there is
   no natural number whose successor is 0.
   ⟩ Likewise taken care of by the Lean kernel giving us `MyNat.noConfusion` ✔

9. If K is a set such that: (i) 0 is in K, and (ii) for every natural
   number n, n being in K implies that S(n) is in K, then K contains
   every natural number.
   ⟩ ...

Reference: https://en.wikipedia.org/wiki/Peano_axioms
-/

/-
### First Peano Axiom (zero)
-/
#check MyNat.zero -- obviously of type `MyNat`

/-
### Second Peano Axiom (reflexivity)
-/
theorem second_peano_axiom (x : MyNat) : x = x := rfl

/-
### Third Peano Axiom (symmetry)
-/
theorem third_peano_axiom (x y : MyNat) (h : x = y) : y = x := h.symm

/-
### Fourth Peano Axiom (transitivity)
-/
theorem fourth_peano_axiom (x y z : MyNat) (h₁ : x = y) (h₂ : y = z) : x = z := by
  rw [h₂] at h₁
  assumption

theorem fourth_peano_axiom' (x y z : MyNat) (h₁ : x = y) (h₂ : y = z) : x = z :=
  Eq.mp (congrArg (fun _a ↦ x = _a) h₂) h₁

theorem fourth_peano_axiom'' (x y z : MyNat) (h₁ : x = y) (h₂ : y = z) : x = z :=
  h₂ ▸ h₁

#print fourth_peano_axiom  -- `Eq.mp (congrArg (fun _a ↦ x = _a) h₂) h₁`
#print fourth_peano_axiom'  -- `Eq.mp (congrArg (fun _a ↦ x = _a) h₂) h₁`
#print fourth_peano_axiom'' -- `h₂ ▸ h₁`

/-
This uses several internals:

```
def Eq.mp {α β : Sort u} (h : α = β) (a : α) : β :=
  h ▸ a

theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
  h ▸ rfl
```

As well as the dependent functional type
-/

/-
### Fifth Peano Axiom

This axiom says:

For all a and b                 -> "untyped"
if b is a natural number        -> b now receives a type
and a = b                       -> stating equality of a typed and untyped element
then a is also a natural number -> inferring a type for a

But saying something is "untyped" is inherently not expressible in Lean / DTT:
*everything* has a type. We also cannot work around this by defining "arbitrary"
types and showing that they need to be `MyNat`; `Eq` cannot take two input arguments
of differing types:

```
example (T₁ T₂ : Type) (a : T₁) (b : T₂) (h₁ : T₁ = MyNat) (h₂ : a = b) : T₂ = MyNat := sorry
example (T₂ : Type) (a : MyNat) (b : T₂) (h₂ : a = b) : T₂ = MyNat := sorry
```

Even cheating by placing a and b in the same type from the start does not lead to
any sensible formulation...

```
example (T : Type) (a b : T) (h₁ : T = MyNat) (h₂ : a = b) : ??? := sorry
```
-/

/-
### Sixth Peano Axiom
-/
#check MyNat.succ    -- MyNat → MyNat

variable (n : MyNat)
#check MyNat.succ n  -- MyNat

/-
### Seventh Peano Axiom

We really have three options:

(I) It needs to be an axiom `axiom {m n : MyNat} (h : succ n = succ m) : n = m` ⨯

(II) It is already true but because some nontrivial work being done in the Lean kernel. ✔

(III) It is trivially true by machinery and types we have already seen. ⨯
-/

-- The Lean kernel already unlocked a recursor for us ...
#check MyNat.rec

-- ... because it (constructively) checked that our definition is logically sound ...
#check MyNat.noConfusion

-- ... which is in fact just a proof of injectivity.
example {m n : MyNat} (h : MyNat.succ n = MyNat.succ m) : n = m := MyNat.noConfusion h id

#print MyNat.noConfusion


/-
## Exercise Block B02
-/

/-
### Eighth Peano Axiom

`MyNat.noConfusion` gives us not only the seventh but also the eighth Peano axiom.

Exercise 2.1
-/
theorem eight_peano_axiom_contradiction (n : MyNat) : 0 ≠ succ n := by
  intro s
  contradiction

#print eight_peano_axiom_contradiction

theorem eight_peano_axiom_trivial (n : MyNat) : 0 ≠ succ n := by
  intro s
  trivial

#print eight_peano_axiom_trivial

theorem eight_peano_axiom (n : MyNat) : 0 ≠ succ n := MyNat.noConfusion

-- Exercise 2.2
theorem zero_ne_one_rw : (0 : MyNat) ≠ 1 := by
  rw [one_eq_succ_zero]
  exact eight_peano_axiom 0

theorem zero_ne_one : (0 : MyNat) ≠ 1 := eight_peano_axiom 0

theorem one_ne_zero : (1 : MyNat) ≠ 0 := zero_ne_one.symm

/-
### Ninth Peano Axiom

`MyNat.rec` unlocks induction for us, which is the ninth and final Peano axiom.

Exercise 2.3
-/

-- We can prove this with the `induction` tactic ...
theorem ninth_peano_axiom (P : MyNat → Prop) (h₁ : P 0) (h₂ : ∀ n, (P n → P n.succ)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact h₁
  | succ n ih => exact h₂ n ih

-- ... but actually this is just `MyNat.rec` given to us by the kernel
theorem ninth_peano_axiom_rec (P : MyNat → Prop) (h₁ : P 0) (h₂ : ∀ n, (P n → P n.succ)) :
    ∀ n, P n := fun n => rec h₁ (fun n ih ↦ h₂ n ih) n

#print axioms ninth_peano_axiom_rec -- no axioms used

/-
Lean is type theory based and sets should not appear in fundamental logical statements
and the construction of natural numbers for us, but if we wanted to directly express
the set theoretic formulation of the ninth Peano axiom, we could by adding `(K : Set MyNat)`
to our assumptions / arguments and noting that `Set.univ {α} := {α | True}`.
-/

theorem ninth_peano_axiom_set' (K : Set MyNat) (h₁ : 0 ∈ K) (h₂ : ∀ n, n ∈ K → n.succ ∈ K) :
    K = Set.univ := by
  ext x
  constructor
  all_goals intro _
  · trivial -- or `intro xk; exact Set.mem_univ x`
  · exact ninth_peano_axiom (fun x => x ∈ K) h₁ h₂ x

#print axioms ninth_peano_axiom_set' -- uses `[propext, Quot.sound]`

example (K : Set MyNat) (h₁ : 0 ∈ K) (h₂ : ∀ n, n ∈ K → n.succ ∈ K) :
    K = Set.univ := by
  ext x
  constructor
  all_goals intro _
  · trivial
  · exact ninth_peano_axiom (fun x => x ∈ K) h₁ h₂ x

end MyNat
