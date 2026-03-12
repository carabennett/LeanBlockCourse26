import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.TFAE

import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Monotone.Basic

/-
## Euclid's theorem: there are infinitely many primes

How exactly is this result stated?

### [Wikipedia](https://en.wikipedia.org/wiki/Euclid%27s_theorem)

"Euclid's theorem (...) asserts that there are infinitely many prime numbers."

### Aigner and Ziegler: Proofs from THE BOOK

* "It shows that the sequence of primes does not end."
* "a finite set {p1,...,pr} cannot be the collection of all prime numbers"
* "We will show that any two Fermat numbers are relatively prime; hence there must be infinitely
   many primes.
* "The set of primes cannot be finite"
* "The function counting the number of primes that are less than or equal to a real number x is
   unbounded, and so there are infinitely many primes"
* "Our final proof goes a considerable step further and demonstrates not only that there are
   infinitely many primes, but also that the series ∑p 1/p diverges.""
-/


/-
You will now have to work with mathlib, i.e., understand its definitions and find its results.

To do this, you should:

(I)   Look up the correct section of the area / type / structure that you are interested in
      and read the comments and basic definitions of at least the main files (`Defs.lean` and
      `Basic.lean`). Either understand the definitions or, if they are too opaque and disappear
      in formal abstraction, find the relevant equivalent definition statements to `rw` with.

(II)  Hover or cmd-click anything that is unclear or unexpected and click through in VS Code.

(III) Use `exact?` or `simp?` whenever you think you have a nuclear expression that *should*
      be in mathlib to try and find it. Often it is advisable to extract the statement into
      separate `example` for this. You can also manually search the files, guess the 
      expected theorem name based on the [mathlib naming convention](https://leanprover-community.github.io/contribute/naming.html),
      use [leansearch.net](https://leansearch.net) or [Loogle](https://loogle.lean-lang.org),
      talk to people on [Is there code for X? on zulip](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Complexity.20theory/with/578655619)
      or ask ChatGPT, Claude, ... with online research tools and maybe even a lean environment.

**When is a `Nat` `Prime`?**

`Mathlib.Data.Nat.Prime.Defs` tells us that `def Prime (p : ℕ) := Irreducible`,
which takes us to `Mathlib.Algebra.Group.Irreducible.Defs`... but really you
probably just want to use one of the many more intuitive definitions and
properties stated in `Mathlib.Data.Nat.Prime.Defs`, for example:

```
variable {p : ℕ}

theorem prime_def : Prime p ↔ 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p := ...

theorem prime_def_lt : Prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1 := ...

theorem prime_def_lt' : Prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m < p → ¬m ∣ p := ...

theorem prime_iff_not_exists_mul_eq :
   p.Prime ↔ 2 ≤ p ∧ ¬ ∃ m n, m < p ∧ n < p ∧ m * n = p := ...
```

### When is a `Set` `Finite` ...

We have already seen in P03 that `Set` is just defined as `Type → Type`.
The relevant part of mathlib to start with is `import Mathlib.Data.Set.Basic`.
For the notion of when a `Set` is `Finite` or `Infinite`, one starting
point in mathlib is `Mathlib.Data.Finite.Defs`. There we see that ...

```
Infinite (s : Set α) : Prop := ¬s.Finite
```

... also captured by ...

```
theorem not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite := ...
```

... and `Finite` itself is an inductively defined type class ...

```
class inductive Finite (α : Sort*) : Prop
   | intro {n : ℕ} : α ≃ Fin n → Finite _
```

... based on the type `Fin n`, capturing `Nat` that are strictly less
than `n`, defined in `Lean.Init.Prelude` as a structure ...

```
structure Fin (n : Nat) where
   mk ::
   val  : Nat
   isLt : LT.lt val n
```

### ... and how does it differ from `Finset`?

In `Mathlib.Data.Finset.Def` we can find the

```
structure Finset (α : Type*) where
  val : Multiset α
  nodup : Nodup val
```

`Mathlib.Data.Set.Finite.Basic` tells you that for any pair of
infinite and finite set we can find an element only in the former ...

```
theorem Set.Infinite.exists_notMem_finset (hs : s.Infinite) (t : Finset α) :
   ∃ a ∈ s, a ∉ t := ...
```

... as well as coerce any `Finite` `Set` to a `Finset`...

```
def Set.Finite.toFinset {s : Set α} (h : s.Finite) : Finset α :=
   @Set.toFinset _ _ h.fintype
```

... while using the fact that an element needs to exist in both versions ...

```
theorem Set.mem_toFinset : a ∈ hs.toFinset ↔ a ∈ s := ...
```  
-/

theorem infinitude_of_primes_tfae : [
   -- **(1) The set of primes is infinite**
   { p : ℕ | p.Prime }.Infinite,

   -- **(2) The subtype of primes is infinite**
   Infinite { p : ℕ // p.Prime },

   -- **(3) For any finite set we can find a prime number outside of it**
   ∀ (S : Finset ℕ), (∃ p ∉ S, p.Prime),

   -- **(4) For any finite set *of primes* we can find a prime outside of it**
   (∀ (S : Finset ℕ) (_ : ∀ s ∈ S, Nat.Prime s), (∃ p ∉ S, p.Prime)),

   -- **(5) For any natural number there exists a prime strictly greater than it**
   (∀ n : ℕ, (∃ p > n, p.Prime)),

   -- **(6) There exists an injection from the Natural numbers into the primes**
   ∃ (P : ℕ → ℕ) (h : P.Injective), (∀ k, (P k).Prime),

   -- **(7) The sequence of primes is strictly monotone increasing**
   StrictMono (Nat.nth Nat.Prime),

   -- **(8) The prime counting function is unbounded**
   -- ∀ n : ℕ, ∃ m, n ≤ Nat.primeCounting m,

   -- **(9) The cardinality of the primes equals ℵ₀**
   -- Cardinal.mk { p : ℕ // p.Prime } = ℵ₀,
   ].TFAE := by

   tfae_have 5 → 6 := by -- Theo
      intro h
      choose P hP using h
      have ⟨pn, hp⟩ := And.intro (fun n ↦ (hP n).left) fun n ↦ (hP n).right

      let f : ℕ → ℕ := fun n ↦ P^[n+1] 0
      use f

      have iterate_nfixed (f : ℕ → ℕ) (h : ∀ x, f x > x) (x n : ℕ) : f^[n+1] x > f^[n] x := by
         rw [Function.iterate_succ']
         exact h (f^[n] x)

      have hfinc: ∀ (n : ℕ), f (n + 1) > f n := by
         unfold f
         intro n
         exact iterate_nfixed P pn 0 (n+1)

      have hfmon : StrictMono f := by exact strictMono_nat_of_lt_succ hfinc

      have hfinj : Function.Injective f := StrictMono.injective hfmon

      have hfprime (n : ℕ) : Nat.Prime (f n) := by
         unfold f
         cases n with
         | zero => exact hp 0
         | succ k => rw [Function.iterate_succ']
                     exact hp (P^[k+1] 0)

      use hfinj

   tfae_have 2 → 3 := by -- Arthur
      intro h S
      let s := Set.infinite_univ_iff.2 h
      let P := @Set.univ { p // Nat.Prime p }
      by_contra a
      push_neg at a
      let PN := P.image Subtype.val
      have PS : PN ⊆ S := by
         rw [Set.subset_def]
         intro k b
         by_contra l
         have x : k ∉ S := by exact Finset.notMem_mono (fun ⦃a⦄ a_1 ↦ a_1) l
         have knp := a k x
         have kp : Nat.Prime k := by
            unfold PN at b
            unfold P at b
            simp at b
            exact b
         contradiction
      have PNI : PN.Infinite := by
         unfold PN
         unfold P
         simp
         exact Set.infinite_coe_iff.mp h
      have SF : (S : Set ℕ).Finite := by exact Finset.finite_toSet S
      obtain ⟨a , inn, nis⟩ := Set.Infinite.exists_notMem_finite PNI SF
      let is := PS inn
      contradiction

   tfae_have 1 → 2 := by -- Onat
      intro h
      exact { not_finite := h }

   tfae_have 1 → 6 := by -- Bohdan
      intro h
      use Nat.nth Nat.Prime
      use Nat.nth_injective h
      intro k
      exact Nat.prime_nth_prime k

   -- tfae_have 3 → 2 := by sorry -- Leonie

   tfae_have 3 → 4 := by -- Alexandra
      intro a b c
      exact a b

   tfae_have 5 → 4 := by -- Sammy
     intro h S _
     rcases Finset.eq_empty_or_nonempty S with SE|SNE
     · use 2
       constructor
       · simp[SE]
       · exact Nat.prime_two
     · obtain ⟨maxS,h₂⟩ := Finset.max_of_nonempty SNE
       obtain⟨p,h₃,h₄⟩ := h maxS
       use p
       constructor
       · have h₅ := GT.gt.lt h₃; exact Finset.notMem_of_max_lt h₅ h₂
       · exact h₄

   tfae_have 6 → 3 := by
      intro h
      rcases h with ⟨P, hP_inj, hP_prime⟩
      intro S
      -- die Menge des Bilds von der inj. Fkt P ist unendlich
      have hR : (Set.range P).Infinite := Set.infinite_range_of_injective hP_inj
      -- ∃ p ∈ ℕ , p ∈ hR ∧ p ∉ S , weil S endl. hR unendlich
      obtain ⟨p, hpR, hpS⟩ := Set.Infinite.exists_notMem_finset hR S
      -- p ∈ hR -> ∃ k ∈ ℕ , p = P k
      rcases hpR with ⟨k, rfl⟩
      -- p = P k ist eine Primzahl
      have g : Nat.Prime (P k) := hP_prime k
      use (P k)


   tfae_have 6 → 1 := by -- Alexander
      rintro ⟨P, hP, hprime⟩
      exact Set.infinite_of_injective_forall_mem hP (fun x => hprime x)

   tfae_have 4 → 1 := by -- Cara
      /-
      We are proving that :
         Given:
            (4) For any finite set *of prime numbers* we can find a prime number outside of it, i.e.
            `(∀ (S : Finset ℕ) (_ : ∀ s ∈ S, Nat.Prime s), (∃ p ∉ S, p.Prime))`.
         Then:
            (1) The set of primes is infinite, i.e. `{ p : ℕ | p.Prime }.Infinite`.
      -/

      -- Introduce our assumption (4)
      intro h

      --- Assume by way of contradiction that the set of primes is finite.
      by_contra P_finite
      push_neg at P_finite

      -- We also define P, the set of primes, to use later in the proof.
      let P := {p | Nat.Prime p}

      -- Now, we show that all numbers in our set are prime, using the theorem `Set.mem_toFinset`
      -- See: (https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Set.mem_toFinset#doc)
      -- This is necessary, since our hypothesis is only for sets of prime numbers.
      obtain (n_in_P_n_prime : (∀ n ∈ P_finite.toFinset, Nat.Prime n)) :=
         fun _ => (@Set.Finite.mem_toFinset ℕ P _ P_finite).mp

      -- We apply our hypothesis, so we get that there exists a
      -- prime not in our finite set of primes
      have _ := h P_finite.toFinset n_in_P_n_prime

      -- Finally, we show that the opposite statement is also true, and we get a contradiction.
      -- See: https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Set.notMem_setOf_iff#doc
      -- For the description of `notMem_setOf_iff`
      obtain (_ : ¬(∃ p ∉ P_finite.toFinset, Nat.Prime p)) := by
         push_neg
         intro p p_not_in_P_finset
         have p_not_in_P := (@Set.Finite.mem_toFinset ℕ P p P_finite).mpr.mt p_not_in_P_finset
         exact Set.notMem_setOf_iff.mp p_not_in_P
      contradiction

   tfae_have 1 → 5 := by -- Tonio
      intro h n
      have ⟨x, y, z⟩ := h.exists_gt n
      exact ⟨x, z, y⟩

   tfae_have 1 → 3 := by -- Nina
      intro P S
      by_contra
      push_neg at this
      have Prime := {p | Nat.Prime p}
      have p := Set.Infinite.exists_notMem_finset P S
      obtain ⟨p, pP, pS⟩ := p
      have not_prime := (this p) pS
      have pPP : Nat.Prime p := pP
      exact not_prime pPP

   tfae_have 3 → 5 := by
      intro rhs n
      obtain ⟨p, p_notin_S, p_prime⟩ := rhs (Finset.range (n + 1))
      exact ⟨p, by simp [Finset.mem_range] at p_notin_S; omega, p_prime⟩

   tfae_have 7 → 1 := fun _ => Nat.infinite_setOf_prime -- Bohdan / Kimia

   tfae_have 1 → 7 := Nat.nth_strictMono -- Bohdan / Kimia

   tfae_finish

