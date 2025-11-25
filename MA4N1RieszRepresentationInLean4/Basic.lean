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

-- Thm: Cauchy-Schwarz inequality
theorem cauchy_schwarz (x y : V) : ‖ ⟪x , y⟫_𝕂 ‖_𝕂 ≤ ‖x‖ * ‖y‖ := by sorry
-- Define orthogonality

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
