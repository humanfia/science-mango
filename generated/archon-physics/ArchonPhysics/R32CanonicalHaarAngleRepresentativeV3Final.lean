import ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# A measurable canonical Haar angle for the V2 concentration chain

The representative of a class in `Real / Integer` is its canonical point in
`[0, 1)`, multiplied by `2 * pi`.  This file discharges the exact coordinate
identification interface in `R32CanonicalFreeBondConcentrationV3Final`; it adds no
probabilistic or long-time hypothesis.
-/

namespace ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final

open ArchonPhysics
open ArchonPhysics.R32HaarScalarTailCleanV4
open MeasureTheory Set

noncomputable section

/-- The canonical angular representative in `[0, 2 * pi)`. -/
def canonicalHaarAngle (phase : UnitAddCircle) : Real :=
  2 * Real.pi *
    (AddCircle.equivIco (1 : Real) 0 phase : Real)

/-- The canonical angular representative is Borel measurable. -/
theorem measurable_canonicalHaarAngle :
    Measurable canonicalHaarAngle := by
  unfold canonicalHaarAngle
  exact measurable_const.mul
    (measurable_subtype_coe.comp
      (AddCircle.measurableEquivIco (1 : Real) 0).measurable)

/-- The real part of the first Fourier character at a real representative is
the ordinary cosine of the corresponding angle. -/
theorem fourier_one_coe_re (x : Real) :
    (fourier 1 (x : UnitAddCircle)).re =
      Real.cos (2 * Real.pi * x) := by
  rw [fourier_coe_apply]
  norm_num
  have hexponent :
      2 * (Real.pi : Complex) * Complex.I * (x : Complex) =
        ((2 * Real.pi * x : Real) : Complex) * Complex.I := by
    push_cast
    ring
  rw [hexponent, Complex.exp_ofReal_mul_I_re]

/-- The canonical measurable angle exactly identifies the shifted first Haar
character with the literal cosine carrier used by the deterministic physical
field. -/
theorem canonicalHaarAngle_isHaarAngleRepresentative :
    IsHaarAngleRepresentative canonicalHaarAngle := by
  intro frequency time phase
  let x : Real :=
    (AddCircle.equivIco (1 : Real) 0 phase : Real)
  have hphase : (x : UnitAddCircle) = phase := by
    dsimp [x]
    exact AddCircle.coe_equivIco
  unfold fixedTimeHaarCarrier fixedTimePhaseAdvance canonicalHaarAngle
  change
    (fourier 1
      (((frequency * time / (2 * Real.pi) : Real) : UnitAddCircle) +
        phase)).re =
      Real.cos
        (frequency * time +
          2 * Real.pi *
            (AddCircle.equivIco (1 : Real) 0 phase : Real))
  change
    (fourier 1
      (((frequency * time / (2 * Real.pi) : Real) : UnitAddCircle) +
        phase)).re =
      Real.cos (frequency * time + 2 * Real.pi * x)
  rw [<- hphase, <- AddCircle.coe_add, fourier_one_coe_re]
  congr 1
  field_simp [Real.pi_ne_zero]

end

end ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final
