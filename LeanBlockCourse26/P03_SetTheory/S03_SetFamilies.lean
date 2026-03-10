/-
This section is mostly inspired by the Set Theory Game:
https://github.com/leanprover-community/lean4game
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Cases
import LeanBlockCourse26.P03_SetTheory.S02_IntersectionsUnions

variable {α : Type*}

#check Set α  -- set with elements of type α
#check Set (Set α) -- set family of sets with elements of type α


/-
# Sets: Set Families
=====================

`S : Set (Set α)` means `S` is a set of sets (a set family) of elements of type `α`.

## Intersections of Set Families

We can use `⋂₀ S`, imported through `Mathlib.Order.SetNotation`, to
denote the intersection of a set family `S`. An element is in `⋂₀ S`
if and only if it is in every set of the family `S`.
-/

example {x : α} {S : Set (Set α)} : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t := by rfl

#check Set.mem_sInter

example (S : Set α) (F : Set (Set α)) (h₁ : S ∈ F) : ⋂₀ F ⊆ S := by
  intro x h
  rw [Set.mem_sInter] at h
  have := h S h₁
  assumption

example (S : Set α) (F : Set (Set α)) (h₁ : S ∈ F) : ⋂₀ F ⊆ S := fun _ h => h S h₁

#check Set.sInter_subset_of_mem

example (F G : Set (Set α)) (h₁ : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x h₂
  rw [Set.mem_sInter] at *
  intro t h₃
  have : t ∈ G := h₁ h₃
  have : x ∈ t := h₂ t this
  assumption

example (F G : Set (Set α)) (h₁ : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := fun _ h₂ t h₃ => h₂ t (h₁ h₃)

/-
## Unions of Set Families

We can also use `⋃₀ S` to denote the union of a set family `S`.
An element is in `⋃₀ S` iff it is in some set of the family `S`.
-/

example {x : α} {S : Set (Set α)} : x ∈ ⋃₀ S ↔ ∃ t ∈ S, x ∈ t := by rfl

#check Set.mem_sUnion

example (S : Set α) (F : Set (Set α)) (h₁ : S ∈ F) : S ⊆ ⋃₀ F := by
  intro x xs
  rw [Set.mem_sUnion]
  use S

example (S : Set α) (F : Set (Set α)) (h₁ : S ∈ F) : S ⊆ ⋃₀ F := fun _ xs => ⟨S, h₁, xs⟩

#check Set.subset_sUnion_of_mem

example (F G : Set (Set α)) (h₁ : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x h
  rw [Set.mem_sUnion] at *
  obtain ⟨t, tf, xt⟩ := h
  have tg := h₁ tf
  use t

example (F G : Set (Set α)) (h₁ : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G :=
  fun _ ⟨t, tf, xt⟩ => ⟨t, h₁ tf, xt⟩

/-
## Exercise Block B01
-/

-- Exercise 1.1
example (R S : Set α) : R ∪ S = ⋃₀ {R, S} := by
  ext x
  constructor
  · rintro (xr | xs)
    · exact ⟨R, Or.inl rfl, xr⟩
    · exact ⟨S, Or.inr rfl, xs⟩
  · rintro ⟨t, ⟨tr | ts, h⟩⟩
    · exact Or.inl (tr ▸ h)
    · exact Or.inr (ts ▸ h)

-- Exercise 1.2
example (F G : Set (Set α)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  constructor
  · rintro ⟨t, tf | tg, h₂⟩
    · left; exact ⟨t, tf, h₂⟩
    · right; exact ⟨t, tg, h₂⟩
  · rintro (⟨t, tf, h₁⟩ | ⟨t, tg, h₁⟩)
    · exact ⟨t, by left; exact tf, h₁⟩
    · exact ⟨t, by right; exact tg, h₁⟩

-- Exercise 1.3
example (S : Set α) (F : Set (Set α)) : ⋃₀ F ⊆ S ↔ ∀ t ∈ F, t ⊆ S := by
  constructor
  · intro h₁ t h₂ x h₃
    exact h₁ ⟨t, h₂, h₃⟩
  · intro h₁ x ⟨t, ht⟩
    exact h₁ t ht.left ht.right

-- Exercise 1.4
example (S : Set α) (F : Set (Set α)) : S ∩ (⋃₀ F) = ⋃₀ {t | ∃ u ∈ F, t = S ∩ u} := by
  ext x
  constructor
  · rintro ⟨hS, t, ht₁, ht₂⟩
    exact ⟨S ∩ t, ⟨t, ht₁, rfl⟩, ⟨hS, ht₂⟩⟩
  · rintro ⟨t, ⟨u, hu₁, rfl⟩, ⟨hS, hu₂⟩⟩
    exact ⟨hS, u, hu₁, hu₂⟩

-- Exercise 1.5
example (R S : Set α) : R ∩ S = ⋂₀ {R, S} := by
  ext x
  constructor
  · rintro ⟨xr, xs⟩ t (rfl | rfl)
    · exact xr
    · exact xs
  · intro h
    exact ⟨h R (by left; rfl), h S (by right; rfl)⟩

-- Exercise 1.6
example (F G : Set (Set α)) : ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
  ext x
  constructor
  · intro h₁
    constructor
    · intro t h₂
      apply h₁ t
      left; exact h₂
    · intro t h₂
      apply h₁ t
      right; exact h₂
  · rintro ⟨h₁, h₂⟩ t (tf | tg)
    · exact h₁ t tf
    · exact h₂ t tg

-- Exercise 1.7
example (S : Set α) (F : Set (Set α)) : S ⊆ ⋂₀ F ↔ ∀ t ∈ F, S ⊆ t := by
  constructor
  · intro h₁ t h₂ x h₃
    exact (h₁ h₃) t h₂
  · intro h₁ x h₂ t h₃
    exact (h₁ t h₃) h₂

-- Exercise 1.8
example (S : Set α) (F G : Set (Set α)) (h₁ : ∀ t ∈ F, S ∪ t ∈ G) : ⋂₀ G ⊆ S ∪ (⋂₀ F) := by
  intro x h₂
  by_cases xs : x ∈ S
  · left; exact xs
  · right
    intro t h₄
    obtain (hS2 | ht) := h₂ (S ∪ t) (h₁ t h₄)
    · by_contra h₆
      exact xs hS2
    · exact ht

-- Exercise 1.9
example (F G H : Set (Set α)) (h₁ : ∀ t ∈ F, ∃ u ∈ G, t ∩ u ∈ H) : (⋃₀ F) ∩ (⋂₀ G) ⊆ ⋃₀ H := by
  intro x ⟨⟨t, ht₁, ht₂⟩, h_subset_all⟩
  obtain ⟨u, hu₁, hu₂⟩ := h₁ t ht₁
  use t ∩ u
  exact ⟨hu₂, ⟨ht₂, h_subset_all u hu₁⟩⟩

-- Exercise 1.10
example (F : Set (Set α)) : (⋃₀ F)ᶜ = ⋂₀ {t | tᶜ ∈ F} := by
  ext x
  constructor
  · intro h₁ t h₂
    rw [Set.mem_compl_iff, Set.mem_sUnion] at h₁
    push_neg at h₁
    have h₃ := h₁ tᶜ h₂
    rw [Set.mem_compl_iff] at h₃
    push_neg at h₃
    exact h₃
  · intro h₁
    rw [Set.mem_compl_iff, Set.mem_sUnion]
    push_neg
    intro t h₂
    exact (h₁ tᶜ) (by rw [Set.mem_setOf, compl_compl]; exact h₂)

-- Exercise 1.11
example (F : Set (Set α)) : (⋂₀ F)ᶜ = ⋃₀ {t | tᶜ ∈ F} := by
  ext x
  constructor
  · intro h₁
    rw [Set.mem_compl_iff, Set.mem_sInter] at h₁
    push_neg at h₁
    obtain ⟨t, ht⟩ := h₁
    use tᶜ
    rw [Set.mem_setOf, compl_compl, Set.mem_compl_iff]
    exact ht
  · intro ⟨u, hu⟩
    rw [Set.mem_compl_iff, Set.mem_sInter]
    push_neg
    use uᶜ
    constructor
    · exact hu.left
    · rw [Set.mem_compl_iff]
      push_neg
      exact hu.right

-- Exercise 1.12
example (F G : Set (Set α)) (h₁ : ∀ t ∈ F, ∃ u ∈ G, t ⊆ u) (h₂ : ∃ t ∈ F, ∀ u ∈ G, u ⊆ t) :
    ∃ s, s ∈ F ∩ G := by
  obtain ⟨t, ht₁, ht₂⟩ := h₂
  obtain ⟨u, hu₁, hu₂⟩ := h₁ t ht₁
  have h₁ : u ⊆ t := ht₂ u hu₁
  have h₂ : t = u := Set.Subset.antisymm hu₂ h₁
  exact ⟨t, ht₁, h₂ ▸ hu₁⟩

-- Exercise 1.13
example (F G : Set (Set α)) : (⋃₀ F) ∩ (⋃₀ G)ᶜ ⊆ ⋃₀ (F ∩ Gᶜ) := by
  intro x ⟨⟨t, ht₁, ht₂⟩, h₁⟩
  use t
  constructor
  · constructor
    · exact ht₁
    · rw [Set.mem_compl_iff]
      by_contra h₂
      rw [Set.mem_compl_iff, Set.mem_sUnion] at h₁
      push_neg at h₁
      exact h₁ t h₂ ht₂
  · exact ht₂

-- Exercise 1.14
example (F G : Set (Set α)) (h₁ : ⋃₀ (F ∩ Gᶜ) ⊆ (⋃₀ F) ∩ (⋃₀ G)ᶜ) :
    (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) := by
  intro x ⟨⟨t, ht₁, ht₂⟩, hg⟩
  use t
  constructor
  · constructor
    · exact ht₁
    · by_contra h
      have : x ∈ ⋃₀ (F ∩ Gᶜ) := ⟨t, ⟨⟨ht₁, h⟩, ht₂⟩⟩
      exact (h₁ this).right hg
  · exact ht₂

-- Exercise 1.15
example (F G : Set (Set α)) : (⋃₀ F) ∩ (⋂₀ G)ᶜ ⊆ ⋃₀ {t | ∃ u ∈ F, ∃ v ∈ G, t = u ∩ vᶜ} := by
  intro x ⟨⟨u, hu⟩, h₁⟩
  rw [Set.mem_compl_iff, Set.mem_sInter] at h₁
  push_neg at h₁
  obtain ⟨v, hv⟩ := h₁
  use u ∩ vᶜ
  constructor
  · use u
    constructor
    · exact hu.left
    · use v
      exact ⟨hv.left, rfl⟩
  · rw [Set.mem_inter_iff, Set.mem_compl_iff]
    exact ⟨hu.right, hv.right⟩

-- Exercise 1.16
example (S : Set α) (h₁ : ∀ F, (⋃₀ F = S → S ∈ F)) : ∃ x, S = {x} := by
  have h₂ := h₁ {t | ∃ x ∈ S, t = {x}}
  have h₃ : ⋃₀ {t | ∃ x ∈ S, t = {x}} = S := by
    ext x
    constructor
    intro h₃
    obtain ⟨t, ht⟩ := h₃
    obtain ⟨y, hy⟩ := ht.left
    rw [hy.right] at ht
    rw [ht.right]
    exact hy.left
    intro h₃
    use {x}
    constructor
    · use x
    · rfl
  obtain ⟨y, hy⟩ := h₂ h₃
  use y
  exact hy.right
