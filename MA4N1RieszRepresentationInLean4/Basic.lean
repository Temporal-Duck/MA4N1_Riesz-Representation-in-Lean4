import Mathlib.Tactic


-- This file is for the formalisation

-- To do:

-- Inner Product Spaces
-- IGNORE THESE FOR NOW
-- Define inner product
-- Define inner product space
-- Define natural norm of an inner product

open InnerProductSpace

variable {𝕂 : Type*} [RCLike 𝕂] {V : Type*} [SeminormedAddCommGroup V] -- Vector space
variable [InnerProductSpace 𝕂 V] -- Inner product space
#check InnerProductSpace
example (x : V) : ⟪x, 0⟫_𝕂 = 0 := by exact inner_zero_right x
example (x : V) : ⟪x, x⟫_𝕂 = ‖x‖^2 := by exact inner_self_eq_norm_sq_to_K x

-- Thm: Cauchy-Schwartz inequality
theorem cauchy_schwartz (x y : V) : ‖⟪x , y⟫_𝕂‖ ≤ ‖x‖ * ‖y‖ := by
  -- Use the built-in Cauchy–Schwarz facts in mathlib.
  -- inner_mul_inner_self_le : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫
  -- call the lemma with explicit instances so Lean doesn't get stuck inferring them
  have h := @inner_mul_inner_self_le 𝕂 V ‹RCLike 𝕂› ‹SeminormedAddCommGroup V›
    ‹InnerProductSpace 𝕂 V› x y
  -- norms of inner products are symmetric, and re ⟪x,x⟫ = ‖x‖^2
  -- Simplify the `inner_mul_inner_self_le` inequality into a squared-norm inequality
  have sq_ineq : ‖⟪x, y⟫_𝕂‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    have h' := by simpa [norm_inner_symm] using h
    simpa [pow_two, ← norm_sq_eq_re_inner x, ← norm_sq_eq_re_inner y] using h'

  -- Take square-roots (both sides are nonnegative) and simplify sqrt-of-square to obtain the result
  calc
      ‖⟪x, y⟫_𝕂‖ = √(‖⟪x, y⟫_𝕂‖ ^ 2) := by simp [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ √(‖x‖ ^ 2 * ‖y‖ ^ 2) := Real.sqrt_le_sqrt sq_ineq
      _ = √(‖x‖ ^ 2) * √(‖y‖ ^ 2) := by rw [Real.sqrt_mul (sq_nonneg ‖x‖) (‖y‖ ^ 2)]
      _ = ‖x‖ * ‖y‖ := by simp

-- Define orthogonality (polymorphic over any inner-product space)
def Orthogonal {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕂 E]
  (x y : E) : Prop := ⟪x, y⟫_𝕂 = 0
notation x " ⟂ " y => Orthogonal x y -- can write x ⟂ y instead of Orthogonal x y

-- Defn: Orthogonal set (maybe use this to update Orthonormal set later?)
def OrthogonalSet {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] (S : Set E) : Prop := ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ⟪x,y⟫_𝕜 = 0


-- Defn: Orthonormal set - using OrthogonalSet
def OrthonormalSet {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] (S : Set E) : Prop :=
  (∀ x ∈ S, ‖x‖ = 1) ∧ OrthogonalSet (𝕜 := 𝕜) S

-- Defn: operator norm for inner product spaces -> using defn in 6.1
noncomputable def OperatorNorm (F : V →L[𝕂] 𝕂) : ℝ :=
  sSup (Set.image (fun x => ‖F x‖) { x : V | ‖x‖ ≤ 1 })

def convexset {V : Type*} [AddCommMonoid V] [Module ℝ V] (S : Set V) : Prop :=
  ∀ (x y : V) (_hx : x ∈ S) (_hy : y ∈ S) (t : ℝ) (_ht : 0 ≤ t ∧ t ≤ 1),
    (1 - t) • x + t • y ∈ S

-- Hilbert Spaces


-- Define Hilbert space (assuming Completeness from Mathlib)
variable {𝕂 H : Type*} [RCLike 𝕂] [SeminormedAddCommGroup H] -- Vector space
variable [InnerProductSpace 𝕂 H] [CompleteSpace H]-- Hilbert space

-- Define Orthogonal complement of a set
noncomputable def OrthogonalComplement (U : Set H) : Set H := {y : H | ∀ x ∈ U, ⟪x, y⟫_𝕂 = 0}
notation U "⟂" => OrthogonalComplement U -- ^^ FIX ABOVE LATER - akrea

-- Prop 5.18: Closest point on a convex set
-- Thm: For U closed linear subspace, H = U ⨁ U^⟂


 -- Riesz Representation Theorem
-- Example 6.10 + Claim
-- Thm: Riesz Representation Theorem

theorem Riesz_rep (G : H →L[𝕂] 𝕂) :
  ∃! y : H,
    (∀ x : H, G x = ⟪x , y⟫_𝕂) ∧
    OperatorNorm G  = ‖y‖ := by
  sorry
