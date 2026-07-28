import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.«4-EC»

/-!
# `IsAdditiveReduction` for a concrete curve at `p = 5`

We instantiate `WeierstrassCurve.IsAdditiveReduction` for `y² = x³ + 5` over `ℚ_[5]` (DVR `ℤ_[5]`).

The `additive` condition `Δ = 0 ∧ c₄ = 0` of the reduction is **proven for real** — pushing through
mathlib's `integralModel`/`residue` machinery and the 5-adic valuation. The ONLY `sorry` is the
`[IsMinimal ℤ_[5] W5padic]` instance (a genuine `MaximalFor` minimality obligation, out of scope).

Test-namespace scratch, NOT part of `ForMathlib`; the shipped definition has no `sorry`.
-/

namespace LeanBridge.Test

open WeierstrassCurve IsLocalRing

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `y² = x³ + 5` over `ℤ`. -/
def WZ : WeierstrassCurve ℤ := ⟨0, 0, 0, 0, 5⟩

/-- `y² = x³ + 5` base-changed to `ℚ_[5]`. -/
noncomputable def W5padic : WeierstrassCurve ℚ_[5] := WZ.map (Int.castRingHom ℚ_[5])

/-- `W5padic` is minimal at 5. (Genuine `MaximalFor` proof obligation — stubbed.) -/
instance : IsMinimal ℤ_[5] W5padic := sorry

/-- `W5padic` has additive reduction at 5: the reduction's `Δ` and `c₄` both vanish.
Only the `IsMinimal` instance above is `sorry`; this proof is real. -/
example : IsAdditiveReduction ℤ_[5] W5padic := by
  refine ⟨?_, ?_⟩
  · -- `Δ` of the reduction vanishes (bad reduction)
    simp only [reduction, map_Δ]
    rw [residue_eq_zero_iff]
    have hΔ : (integralModel ℤ_[5] W5padic).Δ = ((WZ.Δ : ℤ) : ℤ_[5]) := by
      apply IsFractionRing.injective ℤ_[5] ℚ_[5]
      rw [integralModel_Δ_eq, map_intCast]
      simp [W5padic, map_Δ]
    rw [hΔ, mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_int_lt_one_iff_dvd]
    decide
  · -- `c₄` of the reduction vanishes (cusp, not node)
    simp only [reduction, map_c₄]
    have hc₄map : algebraMap ℤ_[5] ℚ_[5] (integralModel ℤ_[5] W5padic).c₄ = W5padic.c₄ := by
      conv_rhs => rw [← baseChange_integralModel_eq ℤ_[5] W5padic]
      simp [WeierstrassCurve.baseChange]
    have hc : (integralModel ℤ_[5] W5padic).c₄ = 0 := by
      apply IsFractionRing.injective ℤ_[5] ℚ_[5]
      rw [map_zero, hc₄map]
      simp [W5padic, map_c₄, show WZ.c₄ = 0 from by decide]
    rw [hc, map_zero]

end LeanBridge.Test
