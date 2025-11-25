import Mathlib.Tactic

-- This file is for the formalisation

-- To do:

namespace IPS -- Inner Product Spaces
-- IGNORE THESE FOR NOW
-- Define inner product
-- Define inner product space
-- Define natural norm of an inner product

open InnerProductSpace

variable {𝕂 V : Type} [RCLike 𝕂] [SeminormedAddCommGroup V] [Module 𝕂 V] -- Vector space
variable [InnerProductSpace 𝕂 V] -- Inner product space

example (x : V) : ⟪x, 0⟫_𝕂 = 0 := by exact inner_zero_right x
example (x : V) : ⟪x, x⟫_𝕂 = ‖x‖^2 := by exact inner_self_eq_norm_sq_to_K x

-- Thm: Cauchy-Schwartz inequality
theorem cauchy_schwartz (x y : V) : ‖⟪x , y⟫_𝕂‖ ≤ ‖x‖ * ‖y‖ := by sorry

-- Define orthogonality
def Orthogonal (x y : V) : Prop := ⟪x, y⟫_𝕂 = 0
notation x " ⟂ " y => Orthogonal x y -- can write x ⟂ y instead of Orthogonal x y

-- Defn: operator norm for inner product spaces -> using defn in 6.1
noncomputable def operatorNorm (F : V →L[𝕂] 𝕂) : ℝ := by sorry
--   might need dual spaces ??
--   sSup {|F x| | x : V, ‖x‖ ≤ 1} ??

end IPS

namespace HS -- Hilbert Spaces
-- Define Hilbert space (assuming Completeness from Mathlib)
-- Define Orthogonal complement of a set
-- Prop 5.18: Closest point on a convex set
-- Thm: For U closed linear subspace, H = U ⨁ U^⟂
end HS

namespace RRT -- Riesz Representation Theorem
-- Example 6.10 + Claim
-- Thm: Riesz Representation Theorem
end RRT
