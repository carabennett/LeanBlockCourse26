/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Cases
import LeanBlockCourse26.P05_NaturalNumbers.S01_Definition

/-
# Addition
=====================

Addition is an operator `+` on two natural numbers that produces a third
natural number and is defined inductively through two axioms:

(i)  n + 0 = n
(ii) m + S(n) = S(m + n)
-/


namespace MyNat


/-
## Defining Addition: Attempt #1

We can define addition axiomatically.
-/

-- We need to define the operator axiomatically since its actual implementation is in the axioms ...
noncomputable axiom my_add (m n : MyNat) : MyNat

-- ... that `my_add n 0 = n` ...
axiom my_add_zero (n : MyNat) : my_add n 0 = n

-- ... and `my_add m n.succ = (my_add m n).succ`
axiom my_add_succ (m n : MyNat) : my_add m n.succ = (my_add m n).succ

-- Note that axiomatically defined types of course still `#check` out ...
#check my_add
#check my_add 0
#check my_add 0 0

-- but we cannot actually `#eval` this addition, so we mark it `noncomputable`
-- #eval my_add 0 0

/-
## Exercise Block B01
-/

-- Exercise 1.1 – Prove that `x + 2 = x + 2`
example (x : MyNat) : my_add x 2 = my_add x 2 := by
  sorry

-- Exercise 1.2 – Prove that `a + (b + 0) + (c + 0) = a + b + c`
example (a b c : MyNat) : my_add a (my_add (my_add b 0) (my_add c 0)) = my_add a (my_add b c) := by
  sorry

-- Exercise 1.3 – Prove that `succ n = n + 1`
theorem succ_eq_add_one' (n : MyNat) : succ n = my_add n 1 := by
  sorry

-- Exercise 1.4 – Prove that `2 + 2 = 4?`
example : my_add 2 2 = 4 := by
  sorry

