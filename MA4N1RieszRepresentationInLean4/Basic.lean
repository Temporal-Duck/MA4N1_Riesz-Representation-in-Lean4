import Mathlib.Tactic

-- INNER PRODUCT SPACES

-- Define inner product
-- Define inner product space
-- Define natural norm of an inner product

open InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] -- Inner product space
variable (W : Submodule ℂ V) -- Subspace of inner product space

example (x : V) : ⟪x, 0⟫_ℂ = 0 := by exact inner_zero_right x
example (x : V) : ⟪x, x⟫_ℂ = ‖x‖^2 := by exact inner_self_eq_norm_sq_to_K x

def BoundedLinearOperator (A : V →ₗ[ℂ] ℂ) : Prop :=
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

-- Parallelogram law with induced norms in V
theorem parallelogram_norm (x y : V) : ‖x+y‖^2 + ‖x-y‖^2 = 2*‖x‖^2 + 2*‖y‖^2 := by
  have : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = RCLike.ofReal (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) := by simp
  rw [this]
  have : 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 = RCLike.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) := by simp
  rw [this]
  push_cast
  let : InnerProductSpace ℝ V := by exact rclikeToReal ℂ V
  simp_rw [← inner_self_eq_norm_sq_to_K]
  rw [← Complex.ofReal_inj]
  push_cast
  have : ∀ z : V, ⟪z, z⟫_ℝ = ⟪z, z⟫_ℂ := by simp only [inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_real_eq_id, id_eq, Complex.ofReal_pow, Complex.coe_algebraMap, implies_true]
  simp_rw [this]
  exact parallelogram x y

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

--lem : ‖ . ‖_op well defined as OperatorNorm is bounded
lemma operator_cts_then_bdd (T : V →L[ℂ] ℂ) :
  BddAbove (Set.image (fun x => ‖T x‖) {x | ‖x‖ ≤ 1}) := by
  unfold BddAbove
  unfold upperBounds
  simp
  obtain ⟨M, hM⟩ := ContinuousLinearMap.bound T
  use M
  dsimp
  intro a ha
  calc
    ‖T a‖ ≤ M * ‖a‖ := by exact hM.2 a
    _ ≤ M := by exact (mul_le_iff_le_one_right hM.1).mpr ha

--thm : ‖T‖_op as a bound for T
theorem operator_bound (x : V) (T : V →L[ℂ] ℂ) : ‖T x‖ ≤  ‖T‖_op * ‖x‖ := by
  by_cases h : x = 0
  · simp_rw [h, ContinuousLinearMap.map_zero T, norm_zero, mul_zero]
    rfl
  · have : ‖x‖ ≠ 0 := by
      apply (not_congr (@norm_eq_zero V _ x)).mpr
      exact h
    have h1 : ‖x‖/‖x‖ = 1 := by exact (div_eq_one_iff_eq this).mpr rfl
    have hle1 : ‖(1/‖x‖)•x‖ ≤ 1 := by
      calc
      ‖(1/‖x‖)•x‖ = ‖x‖/‖x‖ := by
        rw [norm_smul, Real.norm_of_nonneg (one_div_nonneg.mpr (norm_nonneg x))]
        exact one_div_mul_eq_div ‖x‖ ‖x‖
      _ ≤ 1 := by exact div_self_le_one ‖x‖
    calc
      ‖T x‖ = ‖T ((‖x‖/‖x‖)•x)‖ := by rw [h1, one_smul]
      _ = ‖T ((‖x‖*(1/‖x‖))•x)‖ := by rw [div_eq_mul_one_div]
      _ = ‖T (‖x‖•(1/‖x‖)•x)‖ := by rw [mul_smul ‖x‖ (1/‖x‖) x]
      _ = ‖T ((1/‖x‖)•x)‖ * ‖x‖ := by
        rw [ContinuousLinearMap.map_smul_of_tower, norm_smul, norm_norm, mul_comm]
      _ ≤ ‖T‖_op * ‖x‖ := by
        apply mul_le_mul_of_nonneg_right
        · let s := (fun x => ‖T x‖) '' {x : V | ‖x‖ ≤ 1}
          have : ‖T ((1/‖x‖)•x)‖ ∈ s := by exact Set.mem_image_of_mem (fun x ↦ ‖T x‖) hle1
          exact
          ConditionallyCompleteLattice.le_csSup s ‖T ((1/‖x‖)•x)‖ (operator_cts_then_bdd T) this
        · exact norm_nonneg x

-- HILBERT SPACES

-- Define Hilbert space (assuming Completeness from Mathlib)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] -- Hilbert Space
variable (U : Submodule ℂ H) -- U subspace of H (NOTE : using ℂ instead of 𝕂 for now - akira)

-- Defn 5.15
def ConvexSet {V : Type*} [AddCommMonoid V] [Module ℝ V] (S : Set V) : Prop :=
  ∀ (x y : V) (_hx : x ∈ S) (_hy : y ∈ S) (t : ℝ) (_ht : 0 ≤ t ∧ t ≤ 1),
    (1 - t) • x + t • y ∈ S
-- NOTE: Might be better to use 𝕂 = ℂ since notes assume complex Hilbert spaces. It would also
-- make ConvexSet easier to apply as we run into issues treating V as an ℝ-module - Akira

-- Existence of sequence in Prop 5.16
lemma exists_sequence (x : H) (A : Set H) (hne : A.Nonempty) (n : ℕ) :
  ∃ a, a ∈ A ∧ ‖x - a‖^2 ≤ (sInf (Set.range fun a : A => ‖x - a‖))^2 + 1/n := by
  let δ := sInf (Set.range fun a : A => ‖x - a‖)
  sorry

lemma midpoint_closer_to_x (x : H) (A : Set H) (a b : A) :
  ‖x - (1/2) • (a + b)‖^2 = (1/2)*‖x - a‖^2 + (1/2)*‖x - b‖^2 - (1/4)*‖(a : H) - b‖^2 := by
  sorry

-- prop 5.16 edit - akira
theorem closest_point_temp (A : Set H) (hne : A.Nonempty)
(hclosed : IsClosed A) (hconv : ConvexSet A) :
  ∀ x : H, ∃! k : A, ‖x - k‖ = sInf (Set.range fun a : A => ‖x - a‖) := by
  intro x
  let δ := sInf (Set.range fun a : A => ‖x - a‖)
  let t := fun n => Classical.choose (exists_sequence x A hne n)
  have : CauchySeq t := by
    apply NormedAddCommGroup.cauchySeq_iff.mpr
    intro ε hε
    let N := Nat.ceil (4/(ε^2))
    use N
    intro m hm
    intro n hn
    have : δ^2 ≤ δ^2 + 1/(2*n) + 1/(2*m) - (1/4)*‖t n - t m‖^2 := by
      calc
        δ^2 ≤ ‖x - (1/2)•(t n + t m)‖^2 := by
          have hδ : 0 ≤ δ := by
            apply Real.sInf_nonneg
            rintro _ ⟨a, rfl⟩
            exact norm_nonneg (x - a)
          have hle : δ ≤ ‖x - (1/2)•(t n + t m)‖ := by sorry
          exact pow_le_pow_left₀ hδ hle 2
        _ = (1/2)*‖x - t n‖^2 + (1/2)*‖x - t m‖^2 - (1/4)*‖t n - t m‖^2 := by
          #check parallelogram_norm (x - t n) (x - t m)
          sorry
        _ = (1/2)*(δ^2+1/n) + (1/2)*(δ^2+1/m)^2 - (1/4)*‖t n - t m‖^2 := by
          sorry
        _ = δ^2 + 1/(2*n) + 1/(2*m) - (1/4)*‖t n - t m‖^2 := by sorry

    sorry
  obtain ⟨k, hk⟩ := cauchySeq_tendsto_of_complete this -- (t n → k as n → ∞)
  use ⟨k, ?_⟩
  · dsimp
    constructor
    · sorry
    · sorry
  · apply IsClosed.mem_of_tendsto hclosed hk
    unfold Filter.Eventually
    sorry

-- Prop 5.16: Closest point on a convex set
theorem closest_point (A : Set H) (h0 : A.Nonempty) (h1 : IsClosed A) (h2 : ConvexSet A) :
  ∀ x : H, ∃! k : A, ‖x - (k : H)‖ = sInf (Set.range fun a : A => ‖x - (a : H)‖) := by
  intro x
  -- S = {‖x - a‖ | a ∈ A}
  let δ := sInf (Set.range fun a : A => ‖x - (a : H)‖)

  have δ_nonneg : 0 ≤ δ := by
    apply Real.sInf_nonneg
    rintro _ ⟨a, rfl⟩
    exact norm_nonneg (x - (a : H))

  --build seq with ‖x - a_n‖^2 → del^2
  have exist_seq :
    ∀ n : ℕ, ∃ a : A, ‖x - (a : H)‖ ≤ δ + 1/(n+1) := by
    intro n
    have hpos : 0 < (1 : ℝ) / (n + 1) := by
      have hpos' : (0 : ℝ) < (n + 1) := by
        exact_mod_cast Nat.succ_pos n
      exact one_div_pos.mpr hpos'

    -- Use definition of infimum
    have hne : (Set.range fun a : A => ‖x - (a : H)‖).Nonempty := by
      rcases h0 with ⟨a⟩
      refine ⟨‖x - (a : H)‖, ?_⟩
      exact ⟨⟨a, by trivial⟩, rfl⟩

    -- missing

    linarith


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




-- Define Orthogonal complement of a set + show its a linear subspace
def OrthogonalComplement (A : Set H) : Submodule ℂ H where
  carrier := {y : H | ∀ x ∈ A, ⟪x, y⟫_ℂ = 0}
  add_mem' {a b} ha hb := by
    dsimp
    intro x hx
    dsimp at ha
    dsimp at hb
    rw [inner_add_right, (ha x) hx, (hb x) hx, zero_add]
  zero_mem' := by
    dsimp
    exact fun x a ↦ inner_zero_right x
  smul_mem' c {x} hx := by
    dsimp
    intro y hy
    dsimp at hx
    simp_rw [inner_smul_right, (hx y) hy, mul_zero]

notation A "⟂" => OrthogonalComplement A

-- linear subspaces are convex
lemma lin_subspace_convex : ConvexSet W.carrier := by
  unfold ConvexSet
  intro a b ha hb t _
  let T := 1-t
  have h1 : (1 - t) • a ∈ W := by exact Submodule.smul_mem W T ha
  have h2 : t • b ∈ W := by exact Submodule.smul_mem W t hb
  exact W.add_mem' h1 h2

-- u closest point to x in U → x-u ∈ U⟂
lemma sub_closest_in_orth (x : H) (u : U) (h : ‖x - u‖ = sInf (Set.range fun a ↦ ‖x - a‖)) :
  (x - u) ∈ U.carrier ⟂ := by
  sorry

-- Thm 5.20: For U closed linear subspace, H = U ⨁ U^⟂ (requires Prop 5.16)
theorem orthogonal_decompose (h : IsClosed U.carrier) :
  ∀ x : H, ∃! (u : U), ∃! (v : U.carrier ⟂), x = u + v := by
  intro x
  have hne : (U.carrier).Nonempty := by
    use 0
    simp only [Submodule.carrier_eq_coe, SetLike.mem_coe, zero_mem]
  have hconv : ConvexSet U.carrier := by exact lin_subspace_convex U
  obtain ⟨u, hu⟩ := closest_point U.carrier hne h hconv x
  dsimp only [Submodule.carrier_eq_coe, SetLike.coe_sort_coe] at hu
  use u
  dsimp
  constructor
  · let v := x - u
    use ⟨v, ?_⟩
    · dsimp
      unfold v
      refine ⟨?_, ?_⟩
      · grind
      · rintro ⟨y, hy⟩ rfl
        simp
    · by_contra h

      sorry
  · intro y hy
    obtain ⟨v, hv⟩ := hy
    dsimp at hv

    sorry

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

  -- Split into cases G = 0 and G ≠ 0
  by_cases h : ∃ x₀, G x₀ ≠ 0
  -- Case G ≠ 0
  · obtain ⟨x₀, hx₀⟩ := h

    -- Define Kernel, U = ker G
    let U : Submodule ℂ H := {
      carrier := {x : H | G x = 0}
      -- Additive closure
      add_mem' := by
        intro x y hx hy
        dsimp at hx hy ⊢
        simp only [ContinuousLinearMap.map_add, hx, hy, zero_add]
      -- Zero element
      zero_mem' := by
        dsimp
        exact ContinuousLinearMap.map_zero G
      -- Closed under scalar multiplication
      smul_mem' := by
        intro c x hx
        dsimp at hx ⊢
        simp only [ContinuousLinearMap.map_smul, hx, smul_zero]
    }

    --Assume that U is closed
    have U_closed : IsClosed U.carrier := by
      exact ContinuousLinearMap.isClosed_ker G

    -- Get the orthogonal decomposition of x₀
    have ⟨u₀, hu₀_eq, hu₀_unique⟩ := orthogonal_decompose U U_closed x₀
    -- hu₀_eq is the ∃! v, x₀ = u₀ + v part
    obtain ⟨v₀, hv₀_eq, hv₀_unique⟩ := hu₀_eq

    --Get properties of u₀, v₀
    have hu₀_in_U : (u₀ : H) ∈ U.carrier := u₀.property
    have hv₀_in_orth : (v₀ : H) ∈ U.carrier ⟂ := v₀.property
    have hdecomp : x₀ = (u₀ : H) + (v₀ : H) := hv₀_eq

    --prove G(v₀) ≠ 0 if G(x₀) ≠ 0
    have Gv₀_ne : G (v₀ : H) ≠ 0 := by
      intro hcontra
      have : G x₀ = 0 := by
        calc G x₀ = G ((u₀ : H) + (v₀ : H)) := by rw [← hdecomp]
        _ = G (u₀ : H) + G (v₀ : H) := by exact ContinuousLinearMap.map_add G u₀ v₀
        _ = 0 + 0 := by simp [hu₀_in_U, hcontra]
        _ = 0 := zero_add 0
      exact hx₀ this

    -- Show that U⟂ is 1-dimensional

    -- Need to check if there is a problem using the dot product rather than the actual inner product? Should be okay to change later if needed
    have dim_orth_one : ∃ z : H, (∀ w ∈ U.carrier ⟂, ∃ c : ℂ, (w : H) = c • z) ∧ ‖z‖ = 1 := by sorry

    obtain ⟨z, hz_span, hz_norm⟩ := dim_orth_one

    let y := G z • z

    -- Show that G(x) = ⟪x, y⟫ for all x
    have G_eq_inner : ∀ x : H, G x = ⟪x, y⟫_ℂ := by
      intro x
      -- Decompose x using orthogonal_decompose
      have ⟨u, hu_eq, hu_unique⟩ := orthogonal_decompose U U_closed x
      obtain ⟨v, hv_eq, hv_unique⟩ := hu_eq

      -- Get properties of u, v
      have hu_in_U : (u : H) ∈ U.carrier := u.property
      have hv_in_orth : (v : H) ∈ U.carrier ⟂ := v.property
      have hx_decomp : x = (u : H) + (v : H) := hv_eq
      have ⟨c, hc_span⟩ := hz_span (v : H) hv_in_orth

      -- Compute G(x) using linearity and properties of u, v
      have Gx_eq : G x = G (u : H) + G (v : H) := by
        rw [hx_decomp, ContinuousLinearMap.map_add G u v]
      have Gx_eq' : G x = 0 + G (v : H) := by
        rw [Gx_eq, hu_in_U]
      have Gx_eq'' : v = c • z := by exact hc_span
      have final : ⟪x, y⟫_ℂ = ⟪(u : H) + (v : H), G z • z⟫_ℂ := by
        rw [hx_decomp]
      have remove_u : ⟪(u : H), G z • z⟫_ℂ = 0 := by
        sorry
      have inner_eq : ⟪x, y⟫_ℂ = ⟪(v : H), G z • z⟫_ℂ := by
        rw [final, inner_add_left, remove_u, zero_add]
      have final' : ⟪x, y⟫_ℂ = G x := by
        rw [inner_eq]
        rw [Gx_eq'']
        rw [inner_smul_right, inner_smul_left]
        simp_rw [inner_self_eq_norm_sq_to_K]
        rw [hz_norm]
        simp
        have rew_1 : G (v : H) = c * G z := by
          rw [Gx_eq'']
          simp_rw [ContinuousLinearMap.map_smul]
          simp
        rw [mul_comm, RCLike.Complex.conj_eq_iff_real , rew_1.symm]


      sorry
      -- Use that u ∈ U so G(u)=0, v = c•z, then compute ⟪x, y⟫

    -- Show that ‖G‖_op = ‖y‖
    have norm_eq : OperatorNorm G = ‖y‖ := by sorry

    -- Show uniqueness of y
    have uniqueness : ∀ y' : H,
      (∀ x : H, G x = ⟪x, y'⟫_ℂ) ∧ OperatorNorm G = ‖y'‖ → y' = y := by sorry

    use y, ⟨G_eq_inner, norm_eq⟩, uniqueness

  -- Case G = 0
  · push_neg at h
    use 0, ⟨fun x => by simp [h], by sorry⟩
    intro y' ⟨hy'_eq, _⟩
    sorry
    --- End of riesz_rep theorem
