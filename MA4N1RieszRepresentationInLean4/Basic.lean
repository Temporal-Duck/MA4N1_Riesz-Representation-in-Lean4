import Mathlib.Tactic

-- INNER PRODUCT SPACES

-- Define inner product
-- Define inner product space
-- Define natural norm of an inner product

open InnerProductSpace


--variable {𝕂 : Type*} [RCLike 𝕂] -- Field 𝕂 = ℝ or ℂ
variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V] -- Inner product space

example (x : V) : ⟪x, 0⟫_ℂ = 0 := by exact inner_zero_right x
example (x : V) : ⟪x, x⟫_ℂ = ‖x‖^2 := by exact inner_self_eq_norm_sq_to_K x

def BoundedLinearOperator {𝕜 : Type*} [NormedField 𝕜] {V U : Type*}
  [SeminormedAddCommGroup V] [Module 𝕜 V] [SeminormedAddCommGroup U] [Module 𝕜 U]
  (A : V →ₗ[𝕜] U) : Prop :=
  ∃ (M : ℝ), 0 ≤ M ∧ ∀ x : V, ‖A x‖ ≤ M * ‖x‖

-- Thm: Cauchy-Schwartz inequality
theorem cauchy_schwartz (x y : V) : ‖⟪x , y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := by
  -- We want to use the `inner_mul_inner_self_le` lemma
  -- from Mathlib (as it already does most of the work):
  -- inner_mul_inner_self_le : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫
  -- using have to specify all the typeclass instances explicitly so don't have to do it later
  have h  := @inner_mul_inner_self_le ℂ _ _ _ _ x y

  -- norms of inner products are symmetric, and re ⟪x,x⟫ = ‖x‖^2
  -- Rewrite the `inner_mul_inner_self_le` inequality using just norms
  have sq_ineq : ‖⟪x, y⟫_ℂ‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    have h' := by simpa [norm_inner_symm] using h
    simpa [pow_two, ← norm_sq_eq_re_inner x, ← norm_sq_eq_re_inner y] using h'
  -- Take square-roots and simplify sqrt-of-square to get the result
  calc
      ‖⟪x, y⟫_ℂ‖ = √(‖⟪x, y⟫_ℂ‖ ^ 2) := by simp [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ √(‖x‖ ^ 2 * ‖y‖ ^ 2) := Real.sqrt_le_sqrt sq_ineq
      _ = √(‖x‖ ^ 2) * √(‖y‖ ^ 2) := by rw [Real.sqrt_mul (sq_nonneg ‖x‖) (‖y‖ ^ 2)]
      _ = ‖x‖ * ‖y‖ := by simp

-- Prop 4.7
theorem parallelogram (x y : V) : ⟪x+y, x+y⟫_ℂ + ⟪x-y, x-y⟫_ℂ = 2*⟪x, x⟫_ℂ + 2*⟪y, y⟫_ℂ := by
  rw [inner_add_right, inner_add_left, inner_add_left]
  rw [inner_sub_right, inner_sub_left, inner_sub_left]
  ring

-- Prop 4.10
theorem convergence_inner (xn yn : ℕ → V) (x y : V)
  (hxn : ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖xn n - x‖ < ε)
  (hyn : ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖yn n - y‖ < ε) :
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖(⟪xn n, yn n⟫_ℂ - ⟪x, y⟫_ℂ)‖ < ε := by sorry


-- Define orthogonality (polymorphic over any inner-product space)
def Orthogonal (x y : V) : Prop := ⟪x, y⟫_ℂ = 0
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
noncomputable def OperatorNorm (F : V →L[ℂ] ℂ) : ℝ :=
  sSup (Set.image (fun x => ‖F x‖) { x : V | ‖x‖ ≤ 1 })

notation "‖" T "‖_op" => OperatorNorm T

--Useful lemma for proofs
lemma operator_bound (x : V) (T : V →L[ℂ] ℂ) : ‖T x‖ ≤  ‖T‖_op * ‖x‖ := by
  by_cases h : x = 0
  · rw [h, ContinuousLinearMap.map_zero T, norm_zero, norm_zero]
    simp
  · have : x ≠ 0 := by exact h
    have hneq : ‖x‖ ≠ 0 := by sorry
    have one : ‖x‖/‖x‖ = 1 := by exact (div_eq_one_iff_eq hneq).mpr rfl
    calc
      ‖T x‖ = ‖T ((‖x‖/‖x‖)•x)‖ := by sorry
      _ = ‖T ((1/‖x‖)•x)‖ * ‖x‖ := by sorry
      _ ≤ ‖T‖_op * ‖x‖ := by sorry

example (x : V) (h : ¬(x = 0)) : x ≠ 0 := by exact h
example (x : V) (h : ¬(x = 0)) : ‖x‖ ≠ 0 := by sorry
variable (a : ℝ) (x : V)
example (h : a ≠ 0) : a/a = 1 := by exact (div_eq_one_iff_eq h).mpr rfl
#check div_eq_one_iff_eq
example (h : x = 0) : ‖x‖ = 0 := by exact inseparable_zero_iff_norm.mp (congrArg nhds h)
example (p q : Prop) : (p ↔ q) ↔ (¬p ↔ ¬q) := by exact Iff.symm not_iff_not

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
theorem closest_point (A : Set H) (h0 : A.Nonempty)(h1 : IsClosed A) (h2 : ConvexSet A) :
  ∀ x : H, ∃! k : A, ‖x - (k : H)‖ = sInf (Set.range fun a : A => ‖x - (a : H)‖) := by
  intro x
  -- S = {‖x - a‖ | a ∈ A}
  let δ := sInf (Set.range fun a : A => ‖x - (a : H)‖)

  have δ_nonneg : 0 ≤ δ := by
    sorry

  --build seq with ‖x - a_n‖^2 → del^2
  have exist_seq : ∀ n : ℕ, ∃ a : A, ‖x - (a : H)‖^2 ≤ δ^2 + 1/(n+1) := by
    intro n
    sorry

  --build seq and its spec
  let seq := fun n => Classical.choose (exist_seq n)
  let seq_spec := fun n => Classical.choose_spec (exist_seq n)
  --#check seq
  --#check seq_spec

  --build a cauchy seq
  have cauchy : CauchySeq (fun n => (seq n : H)) := by
    sorry

  --A is closed so we can find a_lim in A
  obtain ⟨a_lim, tendsto⟩ := cauchySeq_tendsto_of_complete cauchy
  have a_lim_2 : (a_lim : H) ∈ A := by
    -- A closed + seq in A -> limit in A
    sorry

  -- ||x - a_lim||^2 = del^2
  have norm_limit : ‖x - a_lim‖^2 = δ^2 := by
    -- continuity of norm, limit of seq_spec gives equality
    --Use prop 4.10
    sorry

  -- uniqueness
  have unique : ∀ b : A, ‖x - (b : H)‖ = δ → b = ⟨a_lim, a_lim_2⟩ := by
    intro b hb
    -- get ‖a_lim - b‖ = 0
    --have : δ^2 ≤ ‖x - ((1/2 : ℝ) • (a_lim + (b : H)) : H)‖^2 := by
      --sorry
    -- Need to get ‖a_lim - b‖^2 = 0
    sorry

    sorry




  -- requires parallelogram (Prop 4.7)

-- Thm 5.20: For U closed linear subspace, H = U ⨁ U^⟂ (requires Prop 5.16)
theorem orthogonal_decompose (h : IsClosed U.carrier) :
  ∀ x : H, ∃! (u : U), ∃! (v : U.carrier ⟂), x = u + v := by sorry -- (WILL FIX LATER - akira)

def Projection (P : H →L[ℂ] H) : Prop :=
  ∀ x : H, P (P x) = P x

def OrthogonalProjection (P : H →L[ℂ] H) : Prop :=
  Projection P ∧ ∀ (x y : H), P y = 0 → ⟪P x, y⟫_ℂ = 0

-- Defn: Continuous dual space of H
def DualH := H →L[ℂ] ℂ

-- Do we want to prove its a vector space?
-- Do we need a separate defn for operator norm on DualH?

-- RIESZ REPRESENTATION THEOREM

-- Example 6.10 + Claim
-- Thm: Riesz Representation Theorem

theorem riesz_rep (G : H →L[ℂ] ℂ) :
  ∃! y : H,
    (∀ x : H, G x = ⟪x , y⟫_ℂ) ∧
    OperatorNorm G  = ‖y‖ := by
  sorry
