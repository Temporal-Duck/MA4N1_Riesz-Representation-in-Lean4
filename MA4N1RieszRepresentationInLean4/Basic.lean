import Mathlib.Tactic

-- INNER PRODUCT SPACES

/-
Note that in mathlib, the convention for inner products is that they are conjugate linear in the
first entry. This means we need to define OrthogonalComplement and riesz_rep accordingly.
-/

open InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] -- Inner product space
variable (W : Submodule ℂ V) -- Subspace of inner product space

def BoundedLinearOperator (A : V →ₗ[ℂ] ℂ) : Prop :=
  ∃ (M : ℝ), 0 ≤ M ∧ ∀ x : V, ‖A x‖ ≤ M * ‖x‖

theorem cauchy_schwartz (x y : V) : ‖⟪x , y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := by
  -- Start from: ‖⟪x,y⟫‖ * ‖⟪y,x⟫‖ ≤ re⟪x,x⟫ * re⟪y,y⟫
  have h := @inner_mul_inner_self_le ℂ V _ _ _ x y -- using the inbuilt C-S inequality

  -- rewrite re⟪x,x⟫ and re⟪y,y⟫ as ‖x‖^2 and ‖y‖^2
  have hx : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
    simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  have hy : (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2 := by
    simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) y).symm

  -- squared inequality
  have sq_ineq : ‖⟪x, y⟫_ℂ‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    have h' :
        ‖⟪x, y⟫_ℂ‖ * ‖⟪x, y⟫_ℂ‖ ≤ (⟪x, x⟫_ℂ).re * (⟪y, y⟫_ℂ).re := by
      simpa [norm_inner_symm] using h
    have h'' :
        ‖⟪x, y⟫_ℂ‖ * ‖⟪x, y⟫_ℂ‖ ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
      simpa [hx, hy] using h'
    simpa [pow_two] using h''

  calc
    ‖⟪x, y⟫_ℂ‖ = Real.sqrt (‖⟪x, y⟫_ℂ‖ ^ 2) := by
      simp [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (‖x‖ ^ 2 * ‖y‖ ^ 2) := by
      exact Real.sqrt_le_sqrt sq_ineq
    _ = Real.sqrt ((‖x‖ * ‖y‖) ^ 2) := by
      congr 1
      ring
    _ = ‖x‖ * ‖y‖ := by
      have hxy : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg x) (norm_nonneg y)
      simp [Real.sqrt_sq hxy]


-- Prop 4.7 : Parallelogram law with inner products
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

-- Define orthogonality (polymorphic over any inner-product space)
def Orthogonal (x y : V) : Prop := ⟪x, y⟫_ℂ = 0

notation x " ⟂ " y => Orthogonal x y -- can write x ⟂ y instead of Orthogonal x y

-- Define Orthogonal complement of a set + show its a linear subspace
def OrthogonalComplement (A : Set V) : Submodule ℂ V where
  carrier := {y : V | ∀ x ∈ A, ⟪y, x⟫_ℂ = 0}
  add_mem' {a b} ha hb := by
    dsimp
    intro x hx
    dsimp at ha
    dsimp at hb
    rw [inner_add_left, (ha x) hx, (hb x) hx, zero_add]
  zero_mem' := by
    dsimp
    exact fun x a ↦ inner_zero_left x
  smul_mem' c {x} hx := by
    dsimp
    intro y hy
    dsimp at hx
    simp_rw [inner_smul_left, (hx y) hy, mul_zero]

notation A "⟂" => OrthogonalComplement A

-- Defn: Orthogonal set (maybe use this to update Orthonormal set later?)
def OrthogonalSet {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] (S : Set E) : Prop := ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ⟪x,y⟫_𝕜 = 0

-- Defn: Orthonormal set - using OrthogonalSet
def OrthonormalSet {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] (S : Set E) : Prop :=
  (∀ x ∈ S, ‖x‖ = 1) ∧ OrthogonalSet (𝕜 := 𝕜) S

-- Defn: operator norm for inner product spaces -> using defn in 6.1
noncomputable
def OperatorNorm (F : V →L[ℂ] ℂ) : ℝ :=
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

-- Define Hilbert space over ℂ (assuming Completeness from Mathlib)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] -- Hilbert Space
variable (U : Submodule ℂ H) -- U subspace of H

-- Defn 5.15 : ConvexSet contains line segment connecting any two points in the set
def ConvexSet {V : Type*} [AddCommMonoid V] [Module ℝ V] (S : Set V) : Prop :=
  ∀ (x y : V) (_hx : x ∈ S) (_hy : y ∈ S) (t : ℝ) (_ht : 0 ≤ t ∧ t ≤ 1),
    (1 - t) • x + t • y ∈ S

-- Existence of sequence in Prop 5.16
lemma exists_sequence {H : Type*} [NormedAddCommGroup H] (x : H) (A : Set H) (hne : A.Nonempty)
  (n : ℕ) :
  ∃ a, a ∈ A ∧ ‖x - a‖^2 ≤ (sInf (Set.range fun a : A => ‖x - a‖))^2 + 1/(n+1) := by
  let δ := sInf (Set.range fun a : A => ‖x - a‖)
  have hδ_nonneg : 0 ≤ δ := by
    apply Real.sInf_nonneg
    rintro _ ⟨a, rfl⟩
    exact norm_nonneg (x - a)
  have hpos : 0 < (1 : ℝ) / (n + 1) := by
    exact one_div_pos.mpr (by exact_mod_cast Nat.succ_pos n)
  -- Use definition of infimum
  have hne_range : (Set.range fun a : A => ‖x - a‖).Nonempty := by
    rcases hne with ⟨a⟩
    refine ⟨‖x - a‖, ⟨⟨a, by trivial⟩, rfl⟩⟩

  let eps := 1 / ((2 * δ + 1) * (n + 1) : ℝ)
  have eps_pos : 0 < eps := by
    dsimp [eps]
    have two_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    have two_delta_nonneg : 0 ≤ 2 * δ := by
      apply mul_nonneg two_nonneg hδ_nonneg
    have two_delta_pos : 0 < 2 * δ + 1 := by
      exact lt_add_of_le_of_pos two_delta_nonneg (by norm_num)
    have n1_pos : 0 < (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
    apply one_div_pos.mpr
    apply mul_pos two_delta_pos n1_pos

  have h_inf : ∃ y ∈ Set.range (fun a : A => ‖x - a‖), y < δ + eps := by
    by_contra H
    have hlb : lowerBounds (Set.range fun a : A => ‖x - a‖) (δ + eps) := by
      intro y hy
      have : ¬ (y < δ + eps) := by
        intro hylt
        apply H
        exact ⟨y, hy, hylt⟩
      exact le_of_not_gt this
    have : δ + eps ≤ δ := by
      apply le_csInf hne_range
      exact hlb
    have le_eps_nonpos : eps ≤ 0 := by linarith [this]
    exact (lt_irrefl 0 (lt_of_lt_of_le eps_pos le_eps_nonpos))

  rcases h_inf with ⟨y, ⟨⟨a, ha_eq⟩, hy⟩⟩
  have hy' : ‖x - (a : H)‖ < δ + eps := by simpa [ha_eq] using hy
  have h1 : ‖x - (a : H)‖ ^ 2 ≤ (δ + eps) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg (x - (a : H)))
    exact le_of_lt hy'

  have two_nonneg : 0 ≤ (2 : ℝ) := by norm_num
  have two_delta_nonneg : 0 ≤ 2 * δ := by
    apply mul_nonneg two_nonneg hδ_nonneg
  have two_delta_ge0_add1 : (1 : ℝ) ≤ 2 * δ + 1 := by
    calc
      (1 : ℝ) = 1 + 0 := by ring
      _ ≤ 1 + 2 * δ := by apply add_le_add_left two_delta_nonneg
      _ = 2 * δ + 1 := by ring
  have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have n1_ge1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by
    calc
      (1 : ℝ) = 1 + 0 := by ring
      _ ≤ 1 + n := by apply add_le_add_left hn0
      _ = n + 1 := by ring
  have mult_nonneg_n : 0 ≤ (2 * δ + 1) * (n : ℝ) := by
    apply mul_nonneg
    · linarith [two_delta_nonneg]
    · exact_mod_cast (Nat.zero_le n)
  have step1 : 2 * δ + 1 ≤ (2 * δ + 1) + (2 * δ + 1) * (n : ℝ) := by
    calc
      2 * δ + 1 = (2 * δ + 1) + 0 := by ring
      _ ≤ (2 * δ + 1) + (2 * δ + 1) * (n : ℝ) := by apply add_le_add_left mult_nonneg_n
  have denom_ge1 : 1 ≤ (2 * δ + 1) * (n + 1) := by
    calc
      (1 : ℝ) ≤ 2 * δ + 1 := by exact two_delta_ge0_add1
      _ = (2 * δ + 1) + 0 := by ring
      _ ≤ (2 * δ + 1) + (2 * δ + 1) * (n : ℝ) := by apply add_le_add_left mult_nonneg_n
      _ = (2 * δ + 1) * (n + 1) := by ring
  have two_delta_pos : 0 < 2 * δ + 1 := by
    have : 0 ≤ 2 * δ := mul_nonneg (by norm_num) hδ_nonneg
    exact lt_add_of_le_of_pos this (by norm_num)
  have denom_pos : 0 < (2 * δ + 1) * (n + 1) := by
    have : 0 < (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
    apply mul_pos two_delta_pos this
  have eps_nonneg : 0 ≤ eps := by linarith [eps_pos]
  have eps_sq_le_eps : eps ^ 2 ≤ eps := by
    dsimp [eps]
    have : ((1 / ((2 * δ + 1) * (n + 1))) ^ 2 ≤ 1 / ((2 * δ + 1) * (n + 1))) ↔
      1 ≤ (2 * δ + 1) * (n + 1) := by
      field_simp [denom_pos]
    exact (this.mpr denom_ge1)

  have h2 : (δ + eps) ^ 2 ≤ δ ^ 2 + 1 / (n + 1) := by
    have inter : 2 * δ * eps + eps ^ 2 ≤ 2 * δ * eps + eps := by
      apply add_le_add_left eps_sq_le_eps (2 * δ * eps)
    calc
      (δ + eps) ^ 2 = δ ^ 2 + (2 * δ * eps + eps ^ 2) := by ring
      _ ≤ δ ^ 2 + (2 * δ * eps + eps) := by apply add_le_add_left inter
      _ = δ ^ 2 + (2 * δ + 1) * eps := by ring
      _ = δ ^ 2 + 1 / (n + 1) := by
        dsimp [eps]
        field_simp [denom_pos]
  have hfinal : ‖x - (a : H)‖ ^ 2 ≤ δ ^ 2 + 1 / (n + 1) := by
    exact le_trans h1 h2
  use (a : H), (Subtype.prop a), hfinal


-- midpoint of two points in convex set is in the set
lemma midpoint_mem_of_convex {A : Set V} (hconv : ConvexSet A) (a b : A) :
  (1/(2 : ℝ))•((a : V) + b) ∈ A := by
  simp
  have : 2⁻¹ = (1 : ℝ) - 2⁻¹ := by ring
  conv_rhs =>
    arg 1
    rw [this]
  refine hconv a b ?_ ?_ 2⁻¹ ?_
  · exact Subtype.coe_prop a
  · exact Subtype.coe_prop b
  grind

-- variation of paralellogram law for closest_point
lemma midpoint_closer_to_x {A : Set V} (x : V) (a b : A) :
  ‖x - (1/(2 : ℝ)) • (a + b)‖^2 = (1/2)*‖x - a‖^2 + (1/2)*‖x - b‖^2 - (1/4)*‖(a : V) - b‖^2 := by
  have paralellogram : ‖x - a + (x - b)‖^2 = 2*‖x - a‖^2 + 2*‖x - b‖^2
    - ‖x - a - (x - b)‖^2 := by
    exact eq_sub_of_add_eq (parallelogram_norm (x - a) (x - b))
  have : x - (1/(2 : ℝ)) • (a + b) = (1/(2 : ℝ)) • (x - a + (x - b)) := by
    simp_rw [←add_sub_assoc, sub_add_eq_add_sub,
    ←two_smul ℝ, sub_eq_add_neg, add_assoc, smul_add]
    simp
    grind
  rw [this, norm_smul]
  have : 0 ≤ 1/(2 : ℝ) := by simp
  rw [Real.norm_of_nonneg this, mul_pow, paralellogram]
  simp
  rw [norm_sub_rev (a : V) b]
  ring

-- Prop 5.16: Closest point on a convex set
theorem closest_point (A : Set H) (hne : A.Nonempty)
(hclosed : IsClosed A) (hconv : ConvexSet A) :
  ∀ x : H, ∃! k : A, ‖x - k‖ = sInf (Set.range fun a : A => ‖x - a‖) := by
  intro x
  set δ := sInf (Set.range fun a : A => ‖x - a‖)
  have hδ_nonneg : 0 ≤ δ := by
    apply Real.sInf_nonneg
    rintro _ ⟨a, rfl⟩
    exact norm_nonneg (x - a)
  set t := fun n => Classical.choose (exists_sequence x A hne n)
  have : CauchySeq t := by
    apply NormedAddCommGroup.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (4/(ε^2))
    use N
    intro m hm
    intro n hn
    have : δ^2 ≤ δ^2 + 1/(2*(n+1)) + 1/(2*(m+1)) - (1/4)*‖t n - t m‖^2 := by
      calc
        δ^2 ≤ ‖x - (1/(2 : ℝ))•(t n + t m)‖^2 := by
          have hle : δ ≤ ‖x - (1/(2 : ℝ))•(t n + t m)‖ := by
            apply csInf_le
            · use 0
              unfold lowerBounds
              simp
            use ⟨(1/(2 : ℝ))•(t n + t m), ?_⟩
            refine midpoint_mem_of_convex hconv ⟨(t n), ?_⟩ ⟨(t m), ?_⟩
            · exact (Classical.choose_spec (exists_sequence x A hne n)).1
            exact (Classical.choose_spec (exists_sequence x A hne m)).1
          exact pow_le_pow_left₀ hδ_nonneg hle 2
        _ = (1/2)*‖x - t n‖^2 + (1/2)*‖x - t m‖^2 - (1/4)*‖t n - t m‖^2 := by
          have htn_mem_A := (Classical.choose_spec (exists_sequence x A hne n)).1
          have htm_mem_A := (Classical.choose_spec (exists_sequence x A hne m)).1
          exact midpoint_closer_to_x x ⟨(t n), htn_mem_A⟩ ⟨(t m), htm_mem_A⟩
        _ ≤ (1/2)*(δ^2+1/(n+1)) + (1/2)*(δ^2+1/(m+1)) - (1/4)*‖t n - t m‖^2 := by
          gcongr
          · exact (Classical.choose_spec (exists_sequence x A hne n)).2
          exact (Classical.choose_spec (exists_sequence x A hne m)).2
        _ = δ^2 + 1/(2*(n+1)) + 1/(2*(m+1)) - (1/4)*‖t n - t m‖^2 := by
          grind
    have hε2 : 0 < 4/(ε^2) := by
      simp
      exact sq_pos_of_pos hε
    calc
      ‖t m - t n‖ ≤ √(2/(n+1) + 2/(m+1)) := by
        have h : ‖t n - t m‖^2 ≤ 4*(1/(2*(n+1)) + 1/(2*(m+1))) := by linarith
        rw [mul_add, norm_sub_rev] at h
        simp_rw [mul_one_div] at h
        have : 4/(2*((n : ℝ)+1)) + 4/(2*((m : ℝ)+1)) = 2/(n+1) + 2/(m+1) := by grind
        rw [this] at h
        let := Real.sqrt_le_sqrt h
        simp at this
        exact this
      _ ≤ √(4/N) := by
        gcongr
        have h1 : 2/((n : ℝ)+1) ≤ 2/N := by
          gcongr
          · exact Std.lt_trans hε2 hN
          have hnreal: (N : ℝ) ≤ n := by exact Nat.cast_le.mpr hn
          have hnsucc : (n : ℝ) ≤ n + 1 := by linarith
          linarith [hnreal, hnsucc]
        have h2 : 2/((m : ℝ)+1) ≤ 2/N := by
          gcongr
          · exact Std.lt_trans hε2 hN
          have hmreal: (N : ℝ) ≤ m := by exact Nat.cast_le.mpr hm
          have hmsucc : (m : ℝ) ≤ m + 1 := by linarith
          linarith [hmreal, hmsucc]
        let := add_le_add h1 h2
        ring_nf at this
        ring_nf
        exact this
      _ < ε := by
        let hNnonneg := Std.lt_trans hε2 hN
        have : 0 ≤ ε := by linarith
        rw [← Real.sqrt_sq this]
        apply Real.sqrt_lt_sqrt
        · field_simp
          simp
        field_simp at hN
        field_simp
        rw [mul_comm]
        exact hN
  obtain ⟨k, hk⟩ := cauchySeq_tendsto_of_complete this
  have hkA : k ∈ A := by
    have : ∀ n : ℕ, t n ∈ A := by
      intro n
      exact (Classical.choose_spec (exists_sequence x A hne n)).1
    exact IsClosed.mem_of_tendsto hclosed hk (Filter.Eventually.of_forall this)
  have hkδ : ‖x - k‖ = δ := by
    set T : ℕ → ℝ := fun n => ‖x - t n‖
    have h1 : Filter.Tendsto T Filter.atTop (nhds ‖x - k‖) := by
      set f : H → ℝ := fun y => ‖x - y‖
      have : Continuous f := by continuity
      have : Filter.Tendsto (f ∘ t) Filter.atTop (nhds (f k)) :=
        Continuous.tendsto this k |>.comp hk
      exact this
    have h2 : Filter.Tendsto T Filter.atTop (nhds δ) := by
      set T_squared : ℕ → ℝ := fun n => ‖x - t n‖^2
      set fδ : ℕ → ℝ := fun n => δ^2
      set fδn : ℕ → ℝ := fun n => δ^2 + 1/(n+1)
      have hδT : fδ ≤ T_squared := by
        intro n
        simp [fδ, T_squared]
        have : δ ≤ ‖x - t n‖ := by
          apply csInf_le
          · use 0
            unfold lowerBounds
            simp
          use ⟨t n, ?_⟩
          exact (Classical.choose_spec (exists_sequence x A hne n)).1
        exact pow_le_pow_left₀ hδ_nonneg this 2
      have hTδ : T_squared ≤ fδn := by
        intro n
        simp [T_squared, fδn]
        have := (Classical.choose_spec (exists_sequence x A hne n)).2
        simp at this
        simp [δ, t]
        exact this
      have hδ : Filter.Tendsto fδ Filter.atTop (nhds (δ^2)) := by simp [fδ]
      have hδn : Filter.Tendsto fδn Filter.atTop (nhds (δ^2)) := by
        simp [fδn]
        rw [show δ^2 = δ^2 + 0 by ring]
        apply Filter.Tendsto.add
        · simp
        rw [show (fun (x : ℕ) ↦ ((x : ℝ) + 1)⁻¹) = fun (x : ℕ) => (1 : ℝ)/(x + 1) by
          ext x
          simp [div_eq_inv_mul, mul_comm]]
        apply Filter.Tendsto.div_atTop
        · simp
          rfl
        apply Filter.Tendsto.atTop_add
        · exact tendsto_natCast_atTop_atTop
        · simp
          rfl
      have hT := (tendsto_of_tendsto_of_tendsto_of_le_of_le hδ hδn hδT hTδ).sqrt
      simp [T_squared, Real.sqrt_sq hδ_nonneg] at hT
      simp [T]
      exact hT
    exact tendsto_nhds_unique h1 h2
  have : ∀ k₁ : A, ∀ k₂ : A, (‖x - k₁‖ = δ ∧ ‖x - k₂‖ = δ) → k₁ = k₂ := by
    intro k₁ k₂ ⟨hk₁, hk₂⟩
    have h1 : δ^2 ≤ ‖x - (1/(2 : ℝ))•(k₁ + k₂)‖^2 := by
      have hmem : (1/(2 : ℝ))•((k₁ : H) + k₂) ∈ A := by
        exact midpoint_mem_of_convex hconv ⟨k₁, ?_⟩ ⟨k₂, ?_⟩
      have : δ ≤ ‖x - (1/(2 : ℝ))•(k₁ + k₂)‖ := by
        apply csInf_le
        · use 0
          unfold lowerBounds
          simp
        use ⟨(1/(2 : ℝ))•(k₁ + k₂), hmem⟩
      exact pow_le_pow_left₀ hδ_nonneg this 2
    have h2 : ‖x - (1/(2 : ℝ))•(k₁ + k₂)‖^2 = δ^2 - 1/4*‖(k₁ : H) - k₂‖^2 := by
      let := midpoint_closer_to_x x k₁ k₂
      rw [hk₁, hk₂, ←two_mul] at this
      field_simp at this
      field_simp
      exact this
    have : δ^2 ≤ δ^2 - 1/4*‖(k₁ : H) - k₂‖^2 := by exact le_of_le_of_eq h1 h2
    have : ‖(k₁ : H) - k₂‖^2 ≤ 0 := by linarith
    have : ‖(k₁ : H) - k₂‖^2 = 0 := by linarith [sq_nonneg ‖(k₁ : H) - k₂‖]
    have : ‖(k₁ : H) - k₂‖ = 0 := by exact eq_zero_of_pow_eq_zero this
    have : (k₁ : H) - k₂ = 0 := by exact norm_eq_zero.mp this
    apply Subtype.ext
    exact sub_eq_zero.mp this
  have unique : ∀ y : A, ‖x - y‖ = δ → y = ⟨k, hkA⟩ := by
    intro y hy
    exact (this y ⟨k, hkA⟩ ⟨hy, hkδ⟩)
  use ⟨k, hkA⟩

-- linear subspaces are convex
lemma lin_subspace_convex : ConvexSet W.carrier := by
  unfold ConvexSet
  intro a b ha hb t _
  let T := 1-t
  have h1 : (1 - t) • a ∈ W := by exact Submodule.smul_mem W T ha
  have h2 : t • b ∈ W := by exact Submodule.smul_mem W t hb
  exact W.add_mem' h1 h2

-- makes calc steps easier especially when dealing with ⟨x, x⟩_ℂ
lemma real_sq_eq_complex_sq (a : ℝ) : ((a : ℂ)^2).re = a^2 := by
  set x := a^2
  have : (x : ℂ).re = x := by exact rfl
  calc
    ((a : ℂ)^2).re = (a^2 : ℂ).re := by exact rfl
    _ = a^2 := by
      simp only [x] at this
      push_cast at this
      exact this

-- u closest point to x in U as in closest_point theorem → x-u ∈ U⟂
lemma sub_closest_in_orth (x : V) (u : W) (h : ‖x - u‖ = sInf (Set.range fun (a : W) ↦ ‖x - a‖)) :
  (x - u) ∈ W.carrier ⟂ := by
  set v := x - u
  by_contra h
  unfold OrthogonalComplement at h
  simp at h
  obtain ⟨y', hy'_mem, hy'_ne⟩ := h
  set α := ⟪v, y'⟫_ℂ
  set y := (1/α) • y'
  have hy_one : ⟪v, y⟫_ℂ = 1 := by
    simp_rw [y, inner_smul_right, α]
    rw [one_div, mul_comm]
    apply Complex.mul_inv_cancel
    exact hy'_ne
  obtain ⟨n, hn⟩ := exists_nat_gt (‖y‖ ^ 2)
  have : u + (1/Complex.ofReal n) • y ∈ W := by
    apply Submodule.add_mem
    · exact Submodule.coe_mem u
    · unfold y
      rw [smul_smul]
      exact Submodule.smul_mem W ((1 / n) * (1 / α)) hy'_mem
  set u_n : W := ⟨u + (1/(n : ℂ)) • y, this⟩
  have hn_pos : (0 : ℝ) < n := by
    calc
      0 ≤ ‖y‖^2 := by exact sq_nonneg ‖y‖
      _ < n := by exact hn
  have : ‖x - u_n‖^2 = ‖v‖^2 - 2/n + (1/n^2) * ‖y‖^2 := by
    have : (starRingEnd ℂ) (1/(n : ℂ)) = 1/n := by
          rw [RCLike.conj_eq_iff_real]
          use (1/n)
          simp
    calc
      ‖x - u_n‖^2 = ‖v - (1/(n : ℂ))•y‖^2 := by
        simp only [u_n, v]
        rw [sub_add_eq_sub_sub]
      _ = Complex.re ⟪v - (1/(n : ℂ))•y, v - (1/(n : ℂ))•y⟫_ℂ := by
        rw [inner_self_eq_norm_sq_to_K]
        exact (real_sq_eq_complex_sq ‖v - (1/(n : ℂ)) • y‖).symm
      _ = Complex.re (⟪v, v⟫_ℂ - ⟪v, ((1 : ℂ) / (n : ℂ)) • y⟫_ℂ -
        ⟪(1/(n : ℂ))•y, v⟫_ℂ +
        ⟪(1/(n : ℂ))•y, (1/(n : ℂ))•y⟫_ℂ) := by
        rw [inner_sub_sub_self]
      _ = Complex.re ⟪v, v⟫_ℂ - Complex.re ⟪v, (1/(n : ℂ))•y⟫_ℂ -
        Complex.re ⟪(1/(n : ℂ))•y, v⟫_ℂ +
        Complex.re ⟪(1/(n : ℂ))•y, (1/(n : ℂ))•y⟫_ℂ := by
        simp only [one_div, Complex.add_re, Complex.sub_re]
      _ = Complex.re ⟪v, v⟫_ℂ - Complex.re ⟪v, (1/(n : ℂ))•y⟫_ℂ -
        Complex.re ⟪(1/(n : ℂ))•y, v⟫_ℂ +
        Complex.re ((1/(n : ℂ))^2*⟪y, y⟫_ℂ) := by
        conv_lhs =>
          arg 2
          arg 1
          rw [inner_smul_left, inner_smul_right, ←mul_assoc, this]
        field_simp
      _ = ‖v‖^2 - 2/n + (1/n^2) * ‖y‖^2 := by
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
        rw [←real_sq_eq_complex_sq ‖v‖, ←real_sq_eq_complex_sq ‖y‖]
        rw [inner_smul_left, inner_smul_right, this]
        rw [←@inner_conj_symm _ _ Complex.instRCLike _ _ y v, hy_one]
        have : (starRingEnd ℂ) 1 = 1 := by exact Complex.conj_eq_iff_re.mpr rfl
        rw [this]
        ring_nf
        have : (n : ℂ)⁻¹.re = (n : ℝ)⁻¹ := by simp
        rw [this]
        have : (n : ℝ)⁻¹^2 = ((n : ℂ)⁻¹^2).re := by
          let  := (Complex.ofReal_re ((n : ℝ)⁻¹^2)).symm
          simp at this
          simp
          exact this
        rw [this]
        simp
        have : ((n : ℂ)^2).im = 0 := by
          let := Complex.ofReal_im ((n : ℝ)^2)
          simp at this
          exact this
        simp [this]
  have contradiction1 : ‖x - u_n‖^2 < (sInf (Set.range fun (a : W) ↦ ‖x - a‖))^2 := by
    calc
      ‖x - u_n‖^2 = ‖v‖^2 - 2/n + (1/n^2)*‖y‖^2 := by exact this
      _ < ‖v‖^2 - 2/n + (1/n^2)*n := by gcongr
      _ = ‖v‖^2 - 1/n := by
        field_simp
        ring
      _< (sInf (Set.range fun (a : W) ↦ ‖x - a‖))^2 := by
        have : 0 < 1/(n : ℝ) := by exact one_div_pos.mpr hn_pos
        rw [←h]
        linarith
  have contradiction2 : (sInf (Set.range fun (a : W) ↦ ‖x - a‖))^2 ≤ ‖x - u_n‖^2 := by
    have : sInf (Set.range fun (a : W) ↦ ‖x - a‖) ≤ ‖x - u_n‖ := by
      apply csInf_le
      · use 0
        unfold lowerBounds
        simp
      · use u_n
    gcongr
    refine Real.sInf_nonneg ?_
    rintro _ ⟨a, rfl⟩
    exact norm_nonneg _
  linarith

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
  have huv : ∃! v : U.carrier⟂, x = u + v := by
    set v := x - u
    use ⟨v, ?_⟩
    · dsimp
      unfold v
      refine ⟨?_, ?_⟩
      · grind
      · rintro ⟨y, hy⟩ rfl
        simp
    · exact sub_closest_in_orth U x u hu.1
  constructor
  · exact huv
  · let P : U → Prop := fun y => ∃! v : U.carrier⟂, x = y + v
    have : ∀ u₁ : U, ∀ u₂ : U, (P u₁ ∧ P u₂ → u₁ = u₂) := by
      intro u₁ u₂ ⟨hu₁, hu₂⟩
      obtain ⟨v₁, h₁, _⟩ := hu₁
      obtain ⟨v₂, h₂, _⟩ := hu₂
      have heq : (u₁ : H) - u₂ = v₂ - v₁ := by
        calc
          u₁ - u₂ = (x - v₁) - (x - v₂) := by
            conv_rhs =>
              arg 2
              rw [h₂]
            rw [h₁]
            simp
          _ = v₂ - v₁ := by simp
      have hinner : ⟪(v₂ : H) - v₁, u₁ - u₂⟫_ℂ = 0 := by
        have hu_mem : (u₁ : H) - u₂ ∈ U := by exact Submodule.sub_mem U u₁.2 u₂.2
        have hv_mem : (v₂ : H) - v₁ ∈ U⟂ := by
          have step1 : (v₁ : H) ∈ U⟂ := v₁.2
          have step2 : (v₂ : H) ∈ U⟂ := v₂.2
          apply Submodule.sub_mem
          · exact step2
          · exact step1
        exact hv_mem (↑u₁ - ↑u₂) hu_mem
      have hnorm : ‖u₁ - u₂‖ = 0 := by
        apply sq_eq_zero_iff.mp
        calc
          ‖u₁ - u₂‖^2 = Complex.re ⟪(u₁ : H) - u₂, u₁ - u₂⟫_ℂ := by
            rw [@inner_self_eq_norm_sq_to_K ℂ _ _ _ _ ((u₁ : H) - u₂), ←real_sq_eq_complex_sq]
            simp
          _ = Complex.re ⟪(v₂ : H) - v₁, u₁ - u₂⟫_ℂ := by
            rw [heq]
          _ = 0 := by
            exact
            (AddSemiconjBy.eq_zero_iff (Complex.re 0)
                  (congrFun (congrArg HAdd.hAdd (congrArg Complex.re (id (Eq.symm hinner))))
                    (Complex.re 0))).mp
              rfl
      exact norm_sub_eq_zero_iff.mp hnorm
    have unique : ∀ y, P y → y = u := by
      intro y hy
      exact (this y u ⟨hy, huv⟩)
    exact unique

def Projection (P : H →L[ℂ] H) : Prop :=
  ∀ x : H, P (P x) = P x

def OrthogonalProjection (P : H →L[ℂ] H) : Prop :=
  Projection P ∧ ∀ (x y : H), P y = 0 → ⟪P x, y⟫_ℂ = 0

-- Defn: Continuous dual space of H
def DualH := H →L[ℂ] ℂ

-- Thm: Riesz Representation Theorem

-- Due to Lean being conjugate linear in first entry of inner product,
-- we have to write riesz in this way
theorem riesz_rep (G : H →L[ℂ] ℂ) :
  ∃! y : H,
    (∀ x : H, G x = ⟪y, x⟫_ℂ) ∧
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
        _ = 0 + 0 := by simp [hcontra]
        _ = 0 := zero_add 0
      exact hx₀ this

    have dim_orth_one :
      ∃ z : H, (∀ w ∈ U.carrier ⟂, ∃ c : ℂ, (w : H) = c • z) ∧ ‖z‖ = 1 := by
      classical

      let v : H := (v₀ : H)

      have v_ne0 : v ≠ 0 := by
        intro hv
        apply Gv₀_ne
        simp [v, hv]

      have Gv_ne0 : G v ≠ 0 := by
        simpa [v] using Gv₀_ne

      let z : H := ((1 / ‖v‖ : ℝ) : ℂ) • v

      have hz_norm : ‖z‖ = 1 := by
        have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr v_ne0
        simp [z, norm_smul, hvpos.ne']

      refine ⟨z, ?_, hz_norm⟩
      intro w hw

      let c : ℂ := (G w) / (G v)

      have hw_eq_cv : (w : H) = c • v := by
        have hker : G (w - c • v) = 0 := by
          simp [c, map_sub, Gv_ne0]

        have hU : (w - c • v : H) ∈ U := by
          exact hker

        have hv_mem : v ∈ U.carrier ⟂ := by
          simp [v]

        have hO : (w - c • v : H) ∈ U.carrier ⟂ := by
          exact (U.carrier ⟂).sub_mem hw ((U.carrier ⟂).smul_mem c hv_mem)

        have h0 : (w - c • v : H) = 0 := by
          have : ⟪(w - c • v : H), (w - c • v : H)⟫_ℂ = 0 :=
            hO (w - c • v) hU
          exact (inner_self_eq_zero).1 this

        simpa [sub_eq_zero] using h0
      refine ⟨c * (‖v‖ : ℂ), ?_⟩

      have hvnormR : (‖v‖ : ℝ) ≠ 0 := by
        exact norm_ne_zero_iff.mpr v_ne0

      have hmul : (c * (‖v‖ : ℂ)) * (((1 / ‖v‖ : ℝ) : ℂ)) = c := by
        calc
          (c * (‖v‖ : ℂ)) * (((1 / ‖v‖ : ℝ) : ℂ))
              = c * ((‖v‖ : ℂ) * (((1 / ‖v‖ : ℝ) : ℂ))) := by
                  ring_nf
          _ = c * (1 : ℂ) := by
                  simp [hvnormR, one_div]
          _ = c := by simp

      calc
        (w : H) = c • v := hw_eq_cv
        _ = (c * (‖v‖ : ℂ)) • z := by
          have : (c * (‖v‖ : ℂ)) • z = c • v := by
            calc
              (c * (‖v‖ : ℂ)) • z
                  = (c * (‖v‖ : ℂ)) • ((((1 / ‖v‖ : ℝ) : ℂ)) • v) := by
                      rfl
              _ = ((c * (‖v‖ : ℂ)) * (((1 / ‖v‖ : ℝ) : ℂ))) • v := by
                      simp [smul_smul, mul_assoc]
              _ = c • v := by
                      rw [hmul]
          simp [this]

    obtain ⟨z, hz_span, hz_norm⟩ := dim_orth_one
    -- The below code is for remove_u
    -- Derive hz_in_orth : z ∈ Uᗮ from v₀ ∈ Uᗮ and v₀ = c₀ • z
    -- v₀ ≠ 0 since G v₀ ≠ 0
    have v₀_ne0 : (v₀ : H) ≠ 0 := by
      intro hv
      apply Gv₀_ne
      simp [hv]

    -- v₀ is a scalar multiple of z
    obtain ⟨c₀, hc₀⟩ := hz_span (v₀ : H) hv₀_in_orth

    -- c₀ ≠ 0, otherwise v₀ = 0
    have c₀_ne0 : c₀ ≠ 0 := by
      intro hc
      apply v₀_ne0
      simpa [hc] using hc₀

    -- scale hc₀ by c₀⁻¹
    have hz_eq' :
        (c₀⁻¹ : ℂ) • (v₀ : H) = (c₀⁻¹ * c₀) • z := by
      --apply (c₀⁻¹)• to both sides of hc₀ : v₀ = c₀ • z

      have := congrArg (fun t : H => (c₀⁻¹ : ℂ) • t) hc₀
      simpa [smul_smul] using this

    -- explicitly get (c₀⁻¹ * c₀ : ℂ) = 1 (type-ascription avoids the "expected Type" error)
    have hmul : (c₀⁻¹ * c₀ : ℂ) = 1 := by
      field_simp [c₀_ne0]

    -- now solve for z
    have hz_eq : (c₀⁻¹ : ℂ) • (v₀ : H) = z := by
      calc
        (c₀⁻¹ : ℂ) • (v₀ : H) = (c₀⁻¹ * c₀) • z := hz_eq'
        _ = (1 : ℂ) • z := by simp [hmul]
        _ = z := by simp

    -- conclude z ∈ Uᗮ since Uᗮ is a submodule and v₀ ∈ Uᗮ
    have hz_in_orth : (z : H) ∈ U.carrier ⟂ := by
      have : (c₀⁻¹ : ℂ) • (v₀ : H) ∈ U.carrier ⟂ :=
        Submodule.smul_mem (U.carrier ⟂) (c₀⁻¹ : ℂ) hv₀_in_orth
      simpa [hz_eq] using this


    let y := (starRingEnd ℂ) (G z) • z

    -- Show that G(x) = ⟪x, y⟫ for all x
    have G_eq_inner : ∀ x : H, G x = ⟪y, x⟫_ℂ := by
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
      have final : ⟪y, x⟫_ℂ = ⟪(starRingEnd ℂ) (G z) • z, (u : H) + (v : H)⟫_ℂ := by
        rw [hx_decomp]
      have remove_u :
    ⟪(starRingEnd ℂ) (G z) • z, (u : H)⟫_ℂ = 0 := by
  -- from z ∈ Uᗮ we get ⟪u, z⟫ = 0
        have huz : ⟪z, (u : H)⟫_ℂ = 0 := by
          exact hz_in_orth (u : H) hu_in_U

  -- flip to ⟪z, u⟫ = 0
        have huz' : ⟪(u : H), z⟫_ℂ = 0 := by
          calc
            ⟪(u : H), z⟫_ℂ = (starRingEnd ℂ) (⟪z, (u : H)⟫_ℂ) := by
              simp [inner_conj_symm]
            _ = (starRingEnd ℂ) 0 := by rw [huz]
            _ = 0 := by simp

        simp [inner_smul_left, huz]

      have inner_eq : ⟪y, x⟫_ℂ = ⟪(starRingEnd ℂ) (G z) • z, (v : H)⟫_ℂ := by
        rw [final, inner_add_right, remove_u, zero_add]
      have final' : ⟪y, x⟫_ℂ = G x := by
        rw [inner_eq]
        rw [Gx_eq'']
        rw [inner_smul_left, inner_smul_right]
        rw [inner_self_eq_norm_sq_to_K]
        rw [hz_norm]
        simp
        have rew_1 : G (v : H) = c * G z := by
          rw [Gx_eq'']
          simp_rw [ContinuousLinearMap.map_smul]
          simp
        rw [mul_comm, rew_1.symm]
        rw [Gx_eq']
        simp
      exact final'.symm

    -- Show that ‖G‖_op = ‖y‖
    have norm_eq : OperatorNorm G = ‖y‖ := by
      have hy_norm : ‖y‖ = ‖G z‖ := by
        simp [y, norm_smul, hz_norm]

      -- Upper bound: OperatorNorm G ≤ ‖y‖
      have h_le : OperatorNorm G ≤ ‖y‖ := by
        unfold OperatorNorm
        refine csSup_le ?hs_ne ?bound
        · -- nonempty: 0 is in the set
          refine ⟨0, ?_⟩
          refine ⟨(0 : H), ?_, by simp⟩
          simp
        · intro b hb
          rcases hb with ⟨x, hx, rfl⟩
          -- use YOUR Cauchy–Schwarz lemma
          have hcs : ‖G x‖ ≤ ‖y‖ * ‖x‖ := by
            simpa [G_eq_inner x] using (cauchy_schwartz (V := H) y x)
          have hmul : ‖y‖ * ‖x‖ ≤ ‖y‖ := by
            exact mul_le_of_le_one_right (norm_nonneg y) hx
          exact le_trans hcs hmul

      -- Lower bound: ‖y‖ ≤ OperatorNorm G (test the unit vector z)
      have h_ge : ‖y‖ ≤ OperatorNorm G := by
        unfold OperatorNorm
        have hz_ball : ‖(z : H)‖ ≤ 1 := by
          simp [hz_norm]
        have hz_mem :
            ‖G z‖ ∈ Set.image (fun x : H => ‖G x‖) {x : H | ‖x‖ ≤ 1} :=
          Set.mem_image_of_mem (fun x : H => ‖G x‖) hz_ball
        have : ‖G z‖ ≤ sSup (Set.image (fun x : H => ‖G x‖) {x : H | ‖x‖ ≤ 1}) := by
          exact
            ConditionallyCompleteLattice.le_csSup
              (Set.image (fun x : H => ‖G x‖) {x : H | ‖x‖ ≤ 1})
              ‖G z‖
              (operator_cts_then_bdd (V := H) G)
              hz_mem
        -- rewrite ‖y‖ as ‖G z‖
        simpa [hy_norm] using this

      exact le_antisymm h_le h_ge


    -- Show uniqueness of y
    have uniqueness : ∀ y' : H,
        (∀ x : H, G x = ⟪y', x⟫_ℂ) ∧ OperatorNorm G = ‖y'‖ → y' = y := by
      intro y' hy'
      rcases hy' with ⟨hy'_eq, _⟩
      -- show y' - y = 0
      have h0 : ∀ x : H, ⟪y' - y, x⟫_ℂ = 0 := by
        intro x
        -- ⟪y',x⟫ = ⟪y,x⟫ since both equal G x
        have : ⟪y', x⟫_ℂ = ⟪y, x⟫_ℂ := by
          calc
            ⟪y', x⟫_ℂ = G x := by simp [hy'_eq x]
            _ = ⟪y, x⟫_ℂ := by simp [G_eq_inner x]

        -- ⟪y' - y, x⟫ = ⟪y',x⟫ - ⟪y,x⟫
        simp [inner_sub_left, this]  -- gives 0
      have hself : ⟪y' - y, y' - y⟫_ℂ = 0 := h0 (y' - y)
      -- turn ⟪v,v⟫ = 0 into v = 0
      have : y' - y = 0 := by
        -- inner_self_eq_zero : ⟪v,v⟫ = 0 ↔ v = 0
        exact (inner_self_eq_zero).1 hself
      exact sub_eq_zero.mp this

    use y, ⟨G_eq_inner, norm_eq⟩, uniqueness

  -- Case G = 0
  · push_neg at h
    -- G is identically 0
    have hG0 : ∀ x : H, G x = 0 := by
      intro x
      exact h x

    -- compute OperatorNorm G = 0
    have hOp0 : OperatorNorm G = 0 := by
      unfold OperatorNorm
      -- show the image is exactly {0}
      have himage :
          Set.image (fun x : H => ‖G x‖) {x : H | ‖x‖ ≤ 1} = ({0} : Set ℝ) := by
        ext r
        constructor
        · intro hr
          rcases hr with ⟨x, hx, rfl⟩
          simp [hG0 x]
        · intro hr
          -- r = 0, achieved at x = 0
          have : r = 0 := by simpa using hr
          subst this
          refine ⟨(0 : H), ?_, by simp [hG0 (0 : H)]⟩
          simp
      -- now sSup {0} = 0
      simp [himage]

    -- existence: y = 0 works
    refine ⟨(0 : H), ?_, ?_⟩
    · constructor
      · intro x
        simp [hG0 x]
      · -- OperatorNorm G = ‖0‖
        simp [hOp0]

    -- uniqueness: any y' representing 0 must be 0
    · intro y' hy'
      rcases hy' with ⟨hy'_eq, _⟩
      -- from G=0 and representation, ⟪y', x⟫ = 0 for all x
      have h0 : ∀ x : H, ⟪y', x⟫_ℂ = 0 := by
        intro x
        have : G x = 0 := hG0 x
        -- hy'_eq x : G x = ⟪y', x⟫
        simpa [hy'_eq x] using this
      -- plug x = y' to get y' = 0
      have : y' = 0 := (inner_self_eq_zero).1 (h0 y')
      simp [this]
    --- End of riesz_rep theorem
