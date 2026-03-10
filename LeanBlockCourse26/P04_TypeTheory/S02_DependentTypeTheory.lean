/-
# Dependent Type Theory
=====================

Minimal demos accompanying the theory slides. No Lean-specific machinery —
just the core concepts: dependent functions, the Sort hierarchy, and Prop.
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.ByContra

-- The dependent function type: return type mentions the input value
#check (n : Nat) → Fin (n + 1)
#check Nat → Bool                -- non-dependent: special case

-- The Sort hierarchy: each universe lives in the next
#check Prop     -- Type
#check Type     -- Type 1
#check Type 1   -- Type 2

-- These are actually just notation for `Sort u`
example : Prop = Sort 0 := rfl
example : Type = Sort 1 := rfl
example : Type 1 = Sort 2 := rfl

-- Prop is impredicative: quantifying over types stays in Prop
#check (∀ P : Prop, P → P : Prop)
#check (∀ α : Type, α → α : Type 1)

-- `Prop` is term agnostic ...
def P : Prop := (∀ Q : Prop, Q → Q : Prop)

theorem first_proof : P := by
  intro Q q
  exact q

#print first_proof        -- `fun Q q ↦ q`
#print axioms first_proof -- no axioms

theorem second_proof : P := by
  intro Q q
  by_contra h 
  exact h q 

#print second_proof        -- `fun Q q ↦ Classical.byContradiction fun h ↦ h q`
#print axioms second_proof -- `propext, Classical.choice, Quot.sound`

example : first_proof = second_proof := rfl

-- ... all other types are not
def first_nat : Nat := 2
def second_nat : Nat := 5

-- This obviously won't work...
-- example : first_nat = second_nat := rfl

-- ... and we can in fact proof the opposite
example : first_nat ≠ second_nat := Nat.ne_of_beq_eq_false rfl
