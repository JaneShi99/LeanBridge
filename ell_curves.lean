import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

def E : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, 16⟩

theorem thm : WeierstrassCurve.IsElliptic E := by
  sorry



#check WeierstrassCurve.Affine.Equation E 1 4

def h := E.a₁

def P3 := WeierstrassCurve.Affine.Point.some (W' := E) 1 4

def P4 := WeierstrassCurve.Affine.Point.zero (W' := E)

def P5 := fromAffine.some P4

#check P3 + P4
def P5 := P3 + P3

def P1 := E.zero

#check P1



def P2 := P1 + P1

def P := E.mk 1 4

def Equation (1, 4 : ℚ) : Prop :=
  WeierstrassCurve.Affine.Equation E 1 4 = 0
