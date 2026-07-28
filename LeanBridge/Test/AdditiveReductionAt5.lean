import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Data.ZMod.Basic

/-!
# Concrete example: additive reduction at `p = 5`

The curve `y² = x³ + 5` over `ℚ` has **additive reduction at 5**: reducing modulo 5 (where the
constant term `5 ≡ 0`) gives `y² = x³`, whose unique singular point is a **cusp**. We exhibit this
via the cusp criterion — both `Δ` and `c₄` of the reduced curve vanish (`Δ = 0` ⇒ singular = bad
reduction; `c₄ = 0` ⇒ the singularity is a cusp, not a node ⇒ additive).

NOTE: this demonstrates the *defining condition* of `WeierstrassCurve.IsAdditiveReduction` for
this curve. Producing the full `IsAdditiveReduction ℤ_[5] _` *instance* additionally requires an
`[IsMinimal ℤ_[5] _]` instance, which is a real proof obligation (`IsMinimal` is a `MaximalFor`
over all variable changes), not a computation. Not part of the `ForMathlib` library; build with
`lake build LeanBridge.Test.AdditiveReductionAt5`.
-/

namespace LeanBridge.Test

open WeierstrassCurve

/-- `y² = x³ + 5` as a Weierstrass curve over `ℤ`. -/
def W5 : WeierstrassCurve ℤ := ⟨0, 0, 0, 0, 5⟩

/-- Its reduction modulo 5, a Weierstrass curve over the residue field `ZMod 5`. -/
noncomputable def W5bar : WeierstrassCurve (ZMod 5) := W5.map (Int.castRingHom (ZMod 5))

/-- Bad reduction at 5: the discriminant of the reduction vanishes. -/
example : W5bar.Δ = 0 := by
  unfold W5bar
  rw [map_Δ]
  decide

/-- The singularity is a cusp (not a node): `c₄` of the reduction vanishes ⇒ additive reduction. -/
example : W5bar.c₄ = 0 := by
  unfold W5bar
  rw [map_c₄]
  decide

end LeanBridge.Test
