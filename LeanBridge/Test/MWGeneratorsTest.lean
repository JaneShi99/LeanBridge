import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Torsion

/-! Scratch: given `E(K)` finitely generated, a basis of the free part `E(K) ⧸ torsion`. -/

namespace LeanBridge.Test

open WeierstrassCurve

noncomputable def mwGenerators {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
    [W.IsElliptic] [Module.Finite ℤ (Affine.Point W)] :=
  Module.Free.chooseBasis ℤ (Affine.Point W ⧸ Submodule.torsion ℤ (Affine.Point W))

end LeanBridge.Test
