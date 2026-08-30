import ArchonPhysics.RandomMassAndersonTransferBridge
import ArchonPhysics.ThreeParameterSpectralAveragingDensity

/-!
# Bounded density of the frozen Anderson diagonal potential

At fixed nonzero squared frequency `lambda`, the random-mass harmonic
recurrence has diagonal Anderson potential `lambda * m_i`.  The frozen mass
law is bounded by three times Lebesgue measure.  Linear scaling therefore
gives an explicit density ceiling `3 / |lambda|` for the diagonal potential
law.

This is an unconditional one-site random-operator input.  It does not assert
a Wegner estimate, a fractional-moment bound, or localization by itself.
-/

namespace ArchonPhysics.FrozenAndersonDiagonalPotentialDensity

open ArchonPhysics
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Lebesgue measure scales by the reciprocal absolute determinant under
the one-dimensional Anderson potential chart. -/
theorem map_andersonDiagonalPotential_volume
    {lambda : Real} (hlambda : lambda ≠ 0) :
    Measure.map (andersonDiagonalPotential lambda)
        (volume : Measure Real) =
      ENNReal.ofReal |lambda|⁻¹ • (volume : Measure Real) := by
  change Measure.map (fun mass : Real => lambda * mass)
      (volume : Measure Real) =
    ENNReal.ofReal |lambda|⁻¹ • (volume : Measure Real)
  simpa [smul_eq_mul] using
    (Measure.map_addHaar_smul (μ := (volume : Measure Real)) hlambda)

/-- The frozen one-site Anderson diagonal law has the explicit global
Lebesgue density ceiling `3 / |lambda|` at every nonzero squared frequency.
The multiplicative form avoids coercions between `Real` and `ENNReal`. -/
theorem andersonDiagonalPotentialLaw_le_smul_volume
    {lambda : Real} (hlambda : lambda ≠ 0) :
    andersonDiagonalPotentialLaw lambda ≤
      ((3 : ENNReal) * ENNReal.ofReal |lambda|⁻¹) •
        (volume : Measure Real) := by
  unfold andersonDiagonalPotentialLaw
  let chart : Real → Real := andersonDiagonalPotential lambda
  have hchart : Measurable chart := by
    change Measurable (fun mass : Real => lambda * mass)
    exact measurable_const.mul measurable_id
  calc
    Measure.map chart massCoordinateLaw ≤
        Measure.map chart ((3 : ENNReal) • (volume : Measure Real)) :=
      Measure.map_mono massCoordinateLaw_le_three_smul_volume hchart
    _ = (3 : ENNReal) •
        Measure.map chart (volume : Measure Real) := by
      rw [Measure.map_smul]
    _ = (3 : ENNReal) •
        (ENNReal.ofReal |lambda|⁻¹ • (volume : Measure Real)) := by
      rw [map_andersonDiagonalPotential_volume hlambda]
    _ = ((3 : ENNReal) * ENNReal.ofReal |lambda|⁻¹) •
        (volume : Measure Real) := by
      rw [mul_smul]

/-- Interval small-ball form of the density ceiling. -/
theorem andersonDiagonalPotentialLaw_Icc_le
    {lambda a b : Real} (hlambda : lambda ≠ 0) :
    andersonDiagonalPotentialLaw lambda (Set.Icc a b) ≤
      ((3 : ENNReal) * ENNReal.ofReal |lambda|⁻¹) *
        ENNReal.ofReal (b - a) := by
  have hmeasure := Measure.le_iff.mp
    (andersonDiagonalPotentialLaw_le_smul_volume hlambda)
    (Set.Icc a b) measurableSet_Icc
  simpa [Measure.smul_apply, Real.volume_Icc] using hmeasure

end

end ArchonPhysics.FrozenAndersonDiagonalPotentialDensity
