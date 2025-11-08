import Mathlib.Tactic

-- Can practice Lean here

section numtheory

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
