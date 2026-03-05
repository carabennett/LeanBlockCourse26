/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Batteries.Tactic.Trans
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.TFAE
import Mathlib.Logic.Basic
/-
# Logical Connectives
=====================

This module introduces how to work with compound propositions:
- Conjunction (`AND`, `∧`)
- Disjunction (`OR`, `∨`)
- Equivalence (`↔`) is (essentially but not exactly) just a `(_ → _) ∧ (_ → _)`

All three are right-associative. `↔` is non-associative and cannot be chained
without explicit brackets (use `trans` or `TFAE` instead).

Key tactics:
- `constructor` for splitting compound goals
- `cases` and `rcases` for basic pattern matching
- `obtain` for destructuring hypotheses
- `trans` for chaining equivalences
- `tfae` for working with lists of equivalences
-/

/-
## Working with AND (∧) in the goal

To prove `P ∧ Q`, we need to prove both `P` and `Q`. We can:
- Use `apply And.intro` explicitly
- Use `constructor` as shorthand
- Use angle bracket notation `⟨p, q⟩`

`constructor` is used around 3,000 times in mathlib while
`exact` followed by an `⟨⬝⟩` term is used around 7,000 times.
-/

#check And
#check And.intro  -- takes proofs `(left : a)` and `(right : b)` and produces `(a ∧ b)`

-- Using `apply And.intro` will open two goals (one for `a` and one for `b`)

-- The linter will complain about the following formatting, even though this
-- produces valid Lean code. Without `·` focusing, the proof block simply
-- moves on to the next open goal after each tactic closes the current one.
-- Note that the order matters though, so `exact q; exact p` does not work.
theorem goal_and_apply (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  apply And.intro
  exact p
  exact q

#print goal_and_apply -- produces `⟨p, q⟩`, we will see this notation in a second

-- The notation hides the actual term mode proof
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := And.intro p q

-- This is the recommended and much more readable syntax!
-- But note that we still need to respect the order.
theorem goal_and_apply' (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  apply And.intro
  · exact p -- The `\.` produces · and focuses on the next goal
  · exact q

#print goal_and_apply' -- also produces `⟨p, q⟩` 

-- In order not to have to remember `And.intro` (and the equivalent names
-- for any other structures in the future), we can use the `constructor` tactic
theorem goal_and_constructor (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  · exact p
  · exact q

#print goal_and_constructor -- also produces `⟨p, q⟩`

-- Looking at the actual term modes already introduces the angle bracket
-- notation, which we can also use: `⟨p, q⟩` is notation for `And.intro p q`
-- (assuming `p : P : Prop` and `q : Q : Prop`).
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  exact ⟨p, q⟩

-- Or just use term mode with the `⟨...⟩` notation
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := ⟨p, q⟩

-- First side note: the `⟨...⟩` notation just instantiates a structure ...
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  exact {
    left := p,
    right := q
  }

-- ... but it hides the names by simply ordering the components. By naming
-- them we can also determine the order in which we prove them. Recall P01S05.
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  exact {
    right := q,
    left := p
  }

-- Second side note: recall that we can stack proofs in proofs
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  exact ⟨by assumption, by assumption⟩

-- We can start a tactic mode sub-proof even in term mode
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := ⟨p, by assumption⟩

/-
## Working with AND in a hypothesis

To use a hypothesis `h : P ∧ Q`, we can:

- Access components with `h.1` / `h.2` or `h.left` / `h.right`
- Use `obtain` for destructuring
- Use `cases` and `rcases` for basic pattern matching

`obtain` is used around 15,000 times in mathlib, `cases` 3,000 times,
and `rcases` 7,000 times.
-/

-- Using `.1` / `.2` notation
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor -- because the goal has an `∧`
  · exact h.2
  · exact h.1

-- In term mode
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩

-- Recalling that `And` is just a structure with `left`
-- and `right`, we can also use `.right` / `.left` notation
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.right
  · exact h.left

-- In term mode ...
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := ⟨h.right, h.left⟩

-- ... or also
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := {
  right := h.left,
  left := h.right
}

/-
All of this works for arbitrary structures in Lean, so you can always
(de)construct an instance sequentially (by order of the arguments)

-> `⟨...⟩`, `And.intro ...`, `constructor` with `·`, `.1`, and `.2`

or by specifying the actual names of the components of the structure.

-> `{left := ..., right := ...}`, `.left`, and `.right`

```
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
```
-/

-- Using `obtain` for destructuring
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨p, q⟩ := h -- dissects into `p` and `q` and forgets about `h`
  exact ⟨q, p⟩

-- Using `have` for destructuring
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  have ⟨p, q⟩ := h -- dissects into `p` and `q` but does *not* forget about `h`
  exact ⟨q, p⟩

-- Splitting h up using `cases` (though this is very unintuitive...)
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h
  constructor
  · assumption
  · assumption

-- Using pattern matching with `cases` (recall P01S05)
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h with
  | intro p q => exact ⟨q, p⟩ -- though mathematically this is awful notation

-- Though `rcases` (recursive `cases`) provides a more pleasant syntax here
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  rcases h with ⟨p, q⟩
  exact ⟨q, p⟩

-- `cases'` provides yet another syntax for destructuring, though the linter complains
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases' h with p q
  exact ⟨q, p⟩

-- Note that introduction can be combined with pattern matching
example (P Q : Prop) : (P ∧ Q) → P := by
  intro h
  obtain ⟨p, _⟩ := h
  exact p

theorem and_intro (P Q : Prop) : (P ∧ Q) → P := by
  intro ⟨p, _⟩
  exact p

-- This also works nicely in term mode ...
example (P Q : Prop) : (P ∧ Q) → P := fun ⟨p, _⟩ => p

-- ... which is just nicer notation for the term given by `#print and_intro`
example (P Q : Prop) : (P ∧ Q) → P := 
  fun h => match h with
    | ⟨p, _⟩ => p

-- Note that this is different from
example (P Q : Prop) : P → Q → P := fun p _ => p

/-
## Exercise Block B01
-/

-- Exercise 1.1
-- State and prove that if `P → Q` and `P → R`, then `P → (Q ∧ R)`.
example (P Q R : Prop) (h₁ : P → Q) (h₂ : P → R) : P → (Q ∧ R) := by
  -- First step if we are lost: simplify the goal as much as possible!
  intro p          -- top level connective in goal is `→`, so we use `intro`
  constructor      --  top level connective in goal is `∧`, so we use `constructor`
  · have q : Q := by -- convention: `have` for Prop, `let` for data (→ P04) ...
      exact h₁ p
    exact q
  · have r : R := by -- ... for propositions they behave the same
      exact h₂ p    
    exact r

-- We can simplify ...
example (P Q R : Prop) (h₁ : P → Q) (h₂ : P → R) : P → (Q ∧ R) := by
  intro p
  constructor
  · have q : Q := h₁ p  
    exact q
  · have r : R := h₂ p    
    exact r

-- ... and simplify ...
example (P Q R : Prop) (h₁ : P → Q) (h₂ : P → R) : P → (Q ∧ R) := by
  intro p
  constructor
  · exact h₁ p  
  · exact h₂ p    

-- ... and simplify ...
example (P Q R : Prop) (h₁ : P → Q) (h₂ : P → R) : P → (Q ∧ R) := by
  intro p
  exact ⟨h₁ p, h₂ p⟩

-- Exercise 1.2
-- ... and finally get a simple term proof.
example (P Q R : Prop) (h₁ : P → Q) (h₂ : P → R) : P → (Q ∧ R) :=
  fun p => ⟨h₁ p, h₂ p⟩

/-
## Intermission: The `repeat`, `all_goals`, `try`, and `<;>` tactics

- `repeat tac` repeatedly applies `tac` to the main goal until it fails.
- `all_goals tac` runs `tac` on each goal, concatenating the resulting goals, if any.
- `try tac` attempts to run `tac` without causing failure if it does not apply.
- `tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal.

They are respectively used around 150, 500, 400, and 7000 times in mathlib.
-/

-- We have seen this example before ...
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h       -- or `obtain ⟨p, q⟩ := h` or `rcases h with ⟨p, q⟩`
  constructor
  · assumption
  · assumption

-- ... but now we can do it more compactly with `repeat` ...
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h
  constructor
  repeat assumption

-- ... or alternatively with `all_goals` ...
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h
  constructor
  all_goals assumption

-- ... or with `<;>`
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h
  constructor <;> assumption

-- We can also just `try` to execute a tactic.
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨p, q⟩ := h
  constructor
  all_goals    -- This is needed since otherwise `try exact p` would only try to match goal 1
    try exact p  -- Here the `try` is required ...
    try exact q  -- ... and here of course the `try` is superfluous,

-- Testing the boundaries

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨p, q⟩ := h
  constructor
  repeat exact q  -- succeeds on goal 1 (Q), then fails on goal 2 (P) and stops
  exact p

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨p, q⟩ := h
  constructor
  repeat exact p  -- fails immediately on goal 1 (Q), so this is a no-op
  exact q          -- closes goal 1 (Q)
  exact p          -- closes goal 2 (P)

-- This fails: `all_goals` *actually* applies, *repeat* just tried to apply and stops
-- example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
--   obtain ⟨p, q⟩ := h
--   constructor
--   all_goals
--     exact q
--   exact p

-- For the same reason this fails:
-- example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
--   obtain ⟨p, q⟩ := h
--   constructor <;> exact p
--   exact q

-- So you need `try` in both the `all_goals` ...
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨p, q⟩ := h
  constructor
  all_goals
    try exact q
  exact p

-- ... and the `<;>`
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨p, q⟩ := h
  constructor <;> try exact p
  exact q
  
/-
Basically: chained `<;>` is the same as an indented `all_goals` block.

* `all_goals` applies to all goals but fails if the tactic does not fit one of them
* `repeat` applies to the current goal only and stops on first failure
* `all_goals` combined with `try` applies to all goals and does not fail
-/

/-
## Working with OR (∨) in the goal

To prove P ∨ Q, we need to prove either P or Q. We can:

- Use `apply Or.inl`/`Or.inr` explicitly
- Use `left`/`right` as shorthand
-/

#check Or
#check Or.inl     -- takes a proof `(a : P)` and produces `(P ∨ Q)`
#check Or.inr     -- takes a proof `(b : Q)` and produces `(P ∨ Q)`

-- The most explicit way to deal with `∨` in goal is to
-- directly use `apply Or.inl` or `apply Or.inr`
theorem goal_or_apply (P Q : Prop) (p : P) : P ∨ Q := by
  apply Or.inl
  exact p

#print goal_or_apply -- gives `Or.inl p`

-- Again note that `apply` is destructive since `apply Or.inr` here
-- would have left us with a goal that cannot be proven from the assumptions.
-- example (P Q : Prop) (p : P) : P ∨ Q := by
--   apply Or.inr
--   ... now we are stuck

-- But we could have argued forward here ..
theorem goal_or_exact (P Q : Prop) (p : P) : P ∨ Q := by
  exact Or.inl p

#print goal_or_exact -- also gives `Or.inl p`

-- .. which also gives the term mode proof.
theorem goal_or_term (P Q : Prop) (p : P) : P ∨ Q := Or.inl p

#print goal_or_term -- also gives `Or.inl p`

-- Perhaps more intuitive are the `left` and `right` tactics
theorem goal_or_tactic (P Q : Prop) (p : P) : P ∨ Q := by
  left
  exact p

#print goal_or_tactic -- also gives `Or.inl p`

/-
## Working with OR in a hypothesis

To use `h : P ∨ Q`, we can:
- Use `apply Or.elim` explicitly
- Use `cases` and `rcases`
- Use `obtain` with pattern matching
-/

-- We can deal with `∨` in a hypothesis by applying `Or.elim` directly,
-- again using `·` to structure the proof to the sub-goals. Note that
-- `Or.elim {a b c : Prop} (h : a ∨ b) (left : a → c) (right : b → c) : c`

-- Viewing `Or.elim` as a method, the most obvious thing to do is ...
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  exact Or.elim h p_to_r q_to_r

-- ... or even just use term mode.
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R :=
  Or.elim h p_to_r q_to_r

-- But if we want to get towards what we naturally expect, a case distinction,
-- we need to use `apply` ...
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  apply Or.elim h
  · exact p_to_r  -- Note that you do not have `p : P` in the assumptions here ...
  · exact q_to_r  -- ... and likewise you do not have `q : Q` here.

-- ... but if you really want a case distinction as you expect it, you
-- need to `intro` the hypothesis in each branch.
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  apply Or.elim h
  · intro p
    exact p_to_r p
  · intro q
    exact q_to_r q

-- Note that `apply` just looks for the output of the applied statement in the
-- goal and makes you prove all the assumptions of the applied statement, so
-- if we did not do the partial application `Or.elim h`, we would have gotten
-- three subgoals, since `Or.elim` takes three arguments.
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  apply Or.elim    -- no `h` here
  · exact h
  · exact p_to_r
  · exact q_to_r

/-
This shows why tactics are good to have: you do not need to remember `Or.elim`
or how exactly it is structured. You just use `cases`, `rcases`, or `cases'`
and get exactly the number of cases in the case distinction that you would expect.
-/

-- We can use the `cases` tactic to do a case distinction on a hypothesis ...
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  cases h
  · exact p_to_r (by assumption)
  · exact q_to_r (by assumption)

-- ... and if we want named variables we can also do proper pattern matching
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  cases h with
  | inl p => exact p_to_r p
  | inr q => exact q_to_r q

-- But most likely you should just use `rcases with _ | _` ...
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  rcases h with p | q  -- compare to previous `rcases h with ⟨p, q⟩`
  · exact p_to_r p
  · exact q_to_r q

-- ... or you can use `obtain _ | _ := ...`
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  obtain p | q := h   -- compare to previous `obtain ⟨p, q⟩ := h`
  · exact p_to_r p
  · exact q_to_r q

-- Note that `cases'` is likewise marked as deprecated by the linter.
example (P Q R : Prop) (h : P ∨ Q) (p_to_r : P → R) (q_to_r : Q → R) : R := by
  cases' h with p q
  · exact p_to_r p
  · exact q_to_r q

/-
## Working with nested structures

For more complex structures, we can:
- Use `rcases` for deep pattern matching
- Use `obtain` with nested patterns
-/

-- This is the brute force way ...
example (P Q R : Prop) (h : P ∧ Q ∧ R) : Q := by
  obtain ⟨_, qr⟩ := h
  obtain ⟨q, _⟩ := qr
  exact q

-- ... but even with what we have seen there is a nicer (term mode) proof.
example (P Q R : Prop) (h : P ∧ Q ∧ R) : Q :=
  h.right.left  -- or `h.2.1`

-- But we can also do the deconstruction of `h` in the assumptions more cleanly:
example (P Q R : Prop) (h : P ∧ Q ∧ R) : Q := by
  obtain ⟨_, ⟨q, _⟩⟩ := h
  exact q

-- We can even get rid of the nested brackets ...
example (P Q R : Prop) (h : P ∧ Q ∧ R) : Q := by
  obtain ⟨_, q, _⟩ := h
  exact q

-- ... but only because `∧` is right-associative: `P ∧ Q ∧ R` means `P ∧ (Q ∧ R)`.
example (P Q R : Prop) (h : (P ∧ Q) ∧ R) : Q := by
  obtain ⟨⟨_, q⟩, _⟩ := h  -- here `⟨_, q, _⟩` does not work because of `(P ∧ Q) ∧ R`
  exact q

-- Nested patterns also work with `rcases`.
example (P Q R : Prop) (h : P ∧ Q ∧ R) : Q := by
  rcases h with ⟨_, q, _⟩
  exact q


/-
## The `rintro` tactic

`rintro` allows for more complex pattern matching and is
used around 7500 times in mathlib.
-/

-- Mixing `∧` with `∨` can quickly become very annoying ...
example (P Q R : Prop) : (P ∧ Q) ∨ R → P ∨ R := by
  intro h
  rcases h with pq | r
  · obtain ⟨p, q⟩ := pq
    left
    exact p
  · right
    exact r

-- ... but we can also do mixed nested patterns with `rcases` ...
example (P Q R : Prop) : (P ∧ Q) ∨ R → P ∨ R := by
  intro h
  rcases h with ⟨p, q⟩ | r
  · left
    exact p
  · right
    exact r

-- ... or with `obtain`
example (P Q R : Prop) : (P ∧ Q) ∨ R → P ∨ R := by
  intro h
  obtain ⟨p, q⟩ | r := h
  · left
    exact p
  · right
    exact r

-- But if we also want to do the pattern matching in the
-- `intro` (like we have previously seen) we now need `rintro`.
theorem and_or_rintro (P Q R : Prop) : (P ∧ Q) ∨ R → P ∨ R := by
  rintro (⟨p, q⟩ | r)
  · left
    exact p
  · right
    exact r

-- `#print and_or_rintro` gives us ...
example (P Q R : Prop) : (P ∧ Q) ∨ R → P ∨ R :=
  fun a ↦ Or.casesOn a (fun h ↦ And.casesOn h fun p _ ↦ Or.inl p) fun r ↦ Or.inr r

-- .. which we can simplify to ...
example (P Q R : Prop) : (P ∧ Q) ∨ R → P ∨ R :=
  fun a ↦ Or.casesOn a (fun ⟨p, _⟩ ↦ Or.inl p) fun r ↦ Or.inr r

-- .. which can also be expressed with pattern matching.
example (P Q R : Prop) : (P ∧ Q) ∨ R → P ∨ R :=
  fun h ↦ match h with
  | Or.inl ⟨p, _⟩ => Or.inl p
  | Or.inr r      => Or.inr r

/-
## Exercise Block B02
Try to get the proof with the fewest characters possible! You can use
[ProofGolf](https://github.com/FordUniver/ProofGolf) to measure automatically.
The scoring counts non-whitespace characters, ignoring `;` (since it is
equivalent to a newline) but counting `<;>`.

Hint: try `rintro` with nested structures

Note: `∨` is also right-associative, so the conclusion of Exercise 2.1
parses as `(P ∧ R) ∨ ((P ∧ S) ∨ ((Q ∧ R) ∨ (Q ∧ S)))`. This means
`right; right; left` is needed to reach `Q ∧ R`, for instance.
-/

-- Exercise 2.1 (🥉160 🥈140 🏅110)

-- 158 chars 🥉
example (P Q R S : Prop) : (P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) := by
  intro pqrs
  obtain ⟨pq, rs⟩ := pqrs
  cases' pq with p q
  · cases' rs with r s
    · left; exact ⟨p, r⟩
    · right; left; exact ⟨p, s⟩
  · cases' rs with r s
    · right; right; left; exact ⟨q, r⟩
    · right; right; right; exact ⟨q, s⟩

-- 135 chars 🥈
example (P Q R S : Prop) : (P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) := by
  intro ⟨pq, rs⟩
  cases' pq with p q
  all_goals cases' rs with r s
  · left; exact ⟨p, r⟩
  · right; left; exact ⟨p, s⟩
  · right; right; left; exact ⟨q, r⟩
  · right; right; right; exact ⟨q, s⟩

-- 123 chars 🏅
example (P Q R S : Prop) : (P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) := by
  rintro ⟨p | q, r | s⟩
  · exact Or.inl ⟨p, r⟩
  · exact Or.inr <| Or.inl ⟨p, s⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨q, r⟩
  · exact Or.inr <| Or.inr <| Or.inr ⟨q, s⟩

-- 101 chars 🏅🏅
example (P Q R S : Prop) : (P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) := by
  rintro ⟨p | q, r | s⟩
  · left; exact ⟨p, r⟩
  · right; left; exact ⟨p, s⟩
  · right; right; left; exact ⟨q, r⟩
  · right; right; right; exact ⟨q, s⟩

-- Or we could have cheated with `simp_all`...
example (P Q R S : Prop) : (P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) := by
  rintro ⟨p | q, r | s⟩
  all_goals simp_all -- we will learn about this technique later ...

-- Exercise 2.2 (🥉130 🥈100 🏅70)

-- 124 chars 🥉
example (P Q R S : Prop) : ((P ∧ Q) ∨ R) ∧ S → (P ∨ R) ∧ (Q ∨ R) ∧ S := by
  rintro ⟨h | r, s⟩
  constructor
  · left
    exact h.1
  · constructor
    · left
      exact h.2
    · exact s
  · constructor
    · right
      exact r
    · constructor
      · right
        exact r
      · exact s

-- 122 chars — if you accept the broken linter you can skip some `·` focusing
example (P Q R S : Prop) : ((P ∧ Q) ∨ R) ∧ S → (P ∨ R) ∧ (Q ∨ R) ∧ S := by
  rintro ⟨h | r, s⟩
  constructor
  · left
    exact h.1
  constructor
  · left
    exact h.2
  · exact s
  constructor
  · right
    exact r
  · constructor
    · right
      exact r
    · exact s

-- 95 chars 🥈
example (P Q R S : Prop) : ((P ∧ Q) ∨ R) ∧ S → (P ∨ R) ∧ (Q ∨ R) ∧ S := by
  rintro ⟨⟨p, q⟩ | r, s⟩
  · constructor
    · left; exact p
    · constructor
      · left; exact q
      · exact s
  · exact ⟨Or.inr r, Or.inr r, s⟩

-- 67 chars 🏅
example (P Q R S : Prop) : ((P ∧ Q) ∨ R) ∧ S → (P ∨ R) ∧ (Q ∨ R) ∧ S := by
  rintro ⟨⟨p, q⟩ | r, s⟩
  · exact ⟨Or.inl p, Or.inl q, s⟩
  · exact ⟨Or.inr r, Or.inr r, s⟩

-- Term mode (85 chars)
example (P Q R S : Prop) : ((P ∧ Q) ∨ R) ∧ S → (P ∨ R) ∧ (Q ∨ R) ∧ S :=
  fun ⟨pqr, s⟩ ↦ match pqr with
  | Or.inl ⟨p, q⟩ => ⟨Or.inl p, Or.inl q, s⟩
  | Or.inr r => ⟨Or.inr r, Or.inr r, s⟩

-- This unfortunately does not work ...
-- example (P Q R S : Prop) : ((P ∧ Q) ∨ R) ∧ S → (P ∨ R) ∧ (Q ∨ R) ∧ S :=
--   fun ⟨⟨p, q⟩ | r, s⟩ ↦ ⟨p | _, q | _, s⟩ | ⟨r | _, r | _, s⟩
