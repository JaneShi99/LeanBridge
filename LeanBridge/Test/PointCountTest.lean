import LeanBridge.ForMathlib.«4-EC»
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Scratch: does point-counting the reduction elaborate? (aₚ = #residue field + 1 - #E_ns.) -/

namespace LeanBridge.Test

open WeierstrassCurve IsLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable example (W : WeierstrassCurve K) [IsMinimal R W] : ℤ :=
  (Nat.card (ResidueField R) : ℤ) + 1 - Nat.card (W.reduction R).toAffine.Point

end LeanBridge.Test
