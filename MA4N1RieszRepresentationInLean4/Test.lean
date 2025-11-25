import Mathlib.Tactic

-- Can practice Lean here

namespace numtheory

open Nat

theorem Pooclid_Thm (n : ℕ) : ∃ M, M > n := by
  exact exists_nat_gt n

theorem Euclid_Thm (n : ℕ) : ∃ p, p ≥ n ∧ Nat.Prime p := by
  let p := Nat.minFac (Nat.factorial n + 1)
  have f1 : Nat.factorial n + 1 ≠ 1 := by
    apply Nat.ne_of_gt
    apply succ_lt_succ
    exact factorial_pos n
  have pp : Nat.Prime p := by apply minFac_prime f1
  have np : p ≥ n := sorry -- wip
  exact ⟨p, np, pp⟩

end numtheory

-- https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html#using-theorems-and-lemmas

namespace s_2_2 -- Section 2.2 - Proving identities in algebraic structures

variable {R : Type} [Ring R] -- The following are answers to the exercises

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_neg_cancel, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← right_distrib, zero_add, add_zero]
  exact add_left_cancel h

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  have h : -a + a = b + a := by
    rw [neg_add_cancel, add_comm, h]
  exact add_right_cancel h

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  have h : a + b = -b + b := by
    rw [neg_add_cancel, h]
  exact add_right_cancel h

theorem neg_zero : (-0 : R) = 0 := by -- Must state that -0 : R, otherwise it'll assume -0 0 : ℕ
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  have h : -a + a = 0 := neg_add_cancel a
  exact neg_eq_of_add_eq_zero h

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by -- Given by the fact that 1+1=2 in any ring
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, right_distrib, one_mul]

-- Exercise proofs for group G:
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)
-- Prove the following using only the above axioms
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  -- rw [← inv_mul_cancel a⁻¹, inv_inv]
  sorry

theorem mul_one (a : G) : a * 1 = a := by
  -- rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]
  sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

end s_2_2

namespace s_2_3 -- Section 2.3 - Using theorems and lemmas

open Real

variable (a b c : ℝ)

-- .mp (modus ponens) → , .mp (modus ponens reverse) ←
example (h : a ≤ b) : exp a ≤ exp b := by
  apply exp_le_exp.mpr h

-- linarinth uses lin arithmetic to try to close the proof:
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h'] -- linarinth also uses proof terms in [] parentheses

example : 2*a*b ≤ a^2 + b^2 := by
  linarith [sq_nonneg (a - b)] -- telling lean that (a-b)^2 ≥ 0 is enough for it to complete the pf

-- Exercise proof
example : |a*b| ≤ (a^2 + b^2)/2 := by
  --apply abs_le.mpr
  --have p1 : -((a^2 + b^2)/2)  ≤ a*b := by linarith [sq_nonneg (a+b)]
  --have p2 : a*b ≤ (a^2 + b^2)/2 := by linarith [sq_nonneg (a-b)]
  --exact ⟨p1, p2⟩
  sorry

#check abs_le --Use this for the above

end s_2_3

namespace s_2_4 -- Section 2.4 - More examples using apply and rw



end s_2_4
