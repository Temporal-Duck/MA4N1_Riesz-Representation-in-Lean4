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
