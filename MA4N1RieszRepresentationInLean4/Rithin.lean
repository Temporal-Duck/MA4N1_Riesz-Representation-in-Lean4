import Mathlib.Tactic

variable {ℝ V : Type} [RCLike ℝ] [SeminormedAddCommGroup V] [Module ℝ V] -- Vector space
variable [InnerProductSpace ℝ V] -- Inner product space

def Orthogonal (x y : V) : Prop := ⟪x, y⟫_ℝ = 0
notation x " ⟂ " y => Orthogonal x y

def v1 : V := ![1,1,1]
def v2 : V := ![0,0,0]

#eval Orthogonal v1 v2
#eval v1 ⟂ v2

-- hey rithin ~
-- ive hacked ur computer

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
    have U_closed : IsClosed U.carrier := by sorry

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
      sorry -- Use that u ∈ U so G(u)=0, v = c•z, then compute ⟪x, y⟫

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
