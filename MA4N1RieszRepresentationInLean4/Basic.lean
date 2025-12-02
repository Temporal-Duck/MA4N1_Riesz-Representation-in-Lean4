import Mathlib.Tactic

-- INNER PRODUCT SPACES

-- Define inner product
-- Define inner product space
-- Define natural norm of an inner product

open InnerProductSpace

variable {𝕂 : Type*} [RCLike 𝕂] -- Field 𝕂 = ℝ or ℂ
variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace 𝕂 V] -- Inner product space

example (x : V) : ⟪x, 0⟫_𝕂 = 0 := by exact inner_zero_right x
example (x : V) : ⟪x, x⟫_𝕂 = ‖x‖^2 := by exact inner_self_eq_norm_sq_to_K x

--NOTE: Alternate way of defining subspaces: https://leanprover-community.github.io/mathematics_in_lean/C10_Linear_Algebra.html#subspaces (- akira)
def LinearSubspace {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] (U : Set E) : Prop :=
  ∀ (x y : E) (α β : 𝕜), x ∈ U → y ∈ U → α • x + β • y ∈ U

def ClosedLinearSubspace {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [TopologicalSpace E] (U : Set E) : Prop :=
  LinearSubspace (𝕜 := 𝕜) (U : Set E) ∧ IsClosed U


-- Thm: Cauchy-Schwartz inequality
theorem cauchy_schwartz (x y : V) : ‖⟪x , y⟫_𝕂‖ ≤ ‖x‖ * ‖y‖ := by
  -- We want to use the `inner_mul_inner_self_le` lemma
  -- from Mathlib (as it already does most of the work):
  -- inner_mul_inner_self_le : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫
  -- using have to specify all the typeclass instances explicitly so don't have to do it later
  have h := @inner_mul_inner_self_le 𝕂 V ‹RCLike 𝕂› ‹SeminormedAddCommGroup V›
    ‹InnerProductSpace 𝕂 V› x y


  -- norms of inner products are symmetric, and re ⟪x,x⟫ = ‖x‖^2
  -- Rewrite the `inner_mul_inner_self_le` inequality using just norms
  have sq_ineq : ‖⟪x, y⟫_𝕂‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    have h' := by simpa [norm_inner_symm] using h
    simpa [pow_two, ← norm_sq_eq_re_inner x, ← norm_sq_eq_re_inner y] using h'
  -- Take square-roots and simplify sqrt-of-square to get the result
  calc
      ‖⟪x, y⟫_𝕂‖ = √(‖⟪x, y⟫_𝕂‖ ^ 2) := by simp [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ √(‖x‖ ^ 2 * ‖y‖ ^ 2) := Real.sqrt_le_sqrt sq_ineq
      _ = √(‖x‖ ^ 2) * √(‖y‖ ^ 2) := by rw [Real.sqrt_mul (sq_nonneg ‖x‖) (‖y‖ ^ 2)]
      _ = ‖x‖ * ‖y‖ := by simp

-- Prop 4.7
theorem parallelogram (x y : V) : ⟪x+y, x+y⟫_𝕂 + ⟪x-y, x-y⟫_𝕂 = 2*⟪x, x⟫_𝕂 + 2*⟪y, y⟫_𝕂 := by
  rw [inner_add_right, inner_add_left, inner_add_left]
  rw [inner_sub_right, inner_sub_left, inner_sub_left]
  ring

-- Define orthogonality (polymorphic over any inner-product space)
def Orthogonal {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕂 E]
  (x y : E) : Prop := ⟪x, y⟫_𝕂 = 0
notation x " ⟂ " y => Orthogonal x y -- can write x ⟂ y instead of Orthogonal x y
-- Orthonormal had already been declared (might want to do it ourselves)

-- Defn: Orthogonal set (maybe use this to update Orthonormal set later?)
def OrthogonalSet {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] (S : Set E) : Prop := ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ⟪x,y⟫_𝕜 = 0


-- Defn: Orthonormal set - using OrthogonalSet
def OrthonormalSet {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] (S : Set E) : Prop :=
  (∀ x ∈ S, ‖x‖ = 1) ∧ OrthogonalSet (𝕜 := 𝕜) S

-- LinearIndependent had already been declared (might want to do it ourselves)



-- Defn: operator norm for inner product spaces -> using defn in 6.1
noncomputable def OperatorNorm (F : V →L[𝕂] 𝕂) : ℝ :=
  sSup (Set.image (fun x => ‖F x‖) { x : V | ‖x‖ ≤ 1 })


-- HILBERT SPACES

-- Define Hilbert space (assuming Completeness from Mathlib)
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] -- Hilbert Space
variable (U : Submodule ℂ H) -- U subspace of H (NOTE : using ℂ instead of 𝕂 for now - akira)

-- Define Orthogonal complement of a set
noncomputable def OrthogonalComplement (A : Set H) : Set H := {y : H | ∀ x ∈ A, ⟪x, y⟫_ℂ = 0}
notation A "⟂" => OrthogonalComplement A

-- Defn 5.15
def ConvexSet {V : Type*} [AddCommMonoid V] [Module ℝ V] (S : Set V) : Prop :=
  ∀ (x y : V) (_hx : x ∈ S) (_hy : y ∈ S) (t : ℝ) (_ht : 0 ≤ t ∧ t ≤ 1),
    (1 - t) • x + t • y ∈ S
-- NOTE: Might be better to use 𝕂 = ℂ since notes assume complex Hilbert spaces. It would also
-- make ConvexSet easier to apply as we run into issues treating V as an ℝ-module - Akira

-- Prop 5.16: Closest point on a convex set
theorem closest_point (A : Set H) (h1 : IsClosed A) (h2 : ConvexSet A) :
  ∃! k : A, ∀ x : H, ‖x - k‖ = sInf {‖x - a‖ | a : A} := by
  sorry -- requires parallelogram (Prop 4.7)

-- Thm 5.20: For U closed linear subspace, H = U ⨁ U^⟂ (requires Prop 5.16)
theorem orthogonal_decompose (h : IsClosed U.carrier) :
  ∀ x : H, ∃! (u : U), ∃! (v : U.carrier ⟂), x = u + v := by sorry -- (WILL FIX LATER - akira)

def Projection (P : H →L[ℂ] H) : Prop :=
  ∀ x : H, P (P x) = P x

def OrthogonalProjection (P : H →L[ℂ] H) : Prop :=
  Projection P ∧ ∀ (x y : H), P y = 0 → ⟪P x, y⟫_ℂ = 0

-- Defn: Continuous dual space of H
def DualH := H →L[ℂ] ℂ

-- RIESZ REPRESENTATION THEOREM

-- Example 6.10 + Claim
-- Thm: Riesz Representation Theorem

theorem riesz_rep (G : H →L[ℂ] ℂ) :
  ∃! y : H,
    (∀ x : H, G x = ⟪x , y⟫_ℂ) ∧
    OperatorNorm G  = ‖y‖ := by
  sorry
