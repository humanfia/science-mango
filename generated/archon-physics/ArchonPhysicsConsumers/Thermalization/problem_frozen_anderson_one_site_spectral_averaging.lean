import ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging

/-!
# Consumer: frozen finite-volume one-site spectral averaging inputs

This consumer exposes the sharp frozen diagonal density, the exact local
Green-function Mobius law, and finite-volume one-site threshold interlacing.
It deliberately does not assume a Wegner estimate, an eigenfunction
correlator bound, or localization.
-/

namespace ArchonPhysicsConsumers.Thermalization.ProblemFrozenAndersonOneSiteSpectralAveraging

open ArchonPhysics
open ArchonPhysics.RandomMassAcousticCountingComparison
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open MeasureTheory
open scoped ENNReal Matrix

noncomputable section

/-- Sharp one-site density for the frozen `Uniform[4/5,6/5]` Anderson
diagonal potential. -/
theorem problem_frozenAnderson_sharp_oneSite_density
    {lambda : Real} (hlambda : lambda ≠ 0) :
    andersonDiagonalPotentialLaw lambda ≤
      ((5 / 2 : ENNReal) * ENNReal.ofReal |lambda|⁻¹) •
        (volume : Measure Real) :=
  andersonDiagonalPotentialLaw_le_fiveHalves_smul_volume hlambda

/-- Exact finite-volume local Green-function dependence on one frozen mass
coordinate, with no probabilistic spectral premise. -/
theorem problem_frozenAnderson_oneSite_localGreen_fraction
    {index : Type*} [Fintype index] [DecidableEq index]
    (baseShifted : Matrix index index Complex) (i : index)
    (lambda reference mass : Real)
    (hbase : IsUnit
      (oneSiteAndersonShiftedMatrix baseShifted i
        (andersonDiagonalPotential lambda reference)).det)
    (htarget : IsUnit
      (oneSiteAndersonShiftedMatrix baseShifted i
        (andersonDiagonalPotential lambda mass)).det) :
    frozenOneSiteAndersonLocalGreen baseShifted i lambda mass =
      frozenOneSiteAndersonLocalGreen baseShifted i lambda reference /
        (1 - ((andersonDiagonalPotential lambda mass -
          andersonDiagonalPotential lambda reference : Real) : Complex) *
            frozenOneSiteAndersonLocalGreen baseShifted i lambda reference) :=
  frozenOneSiteAndersonLocalGreen_eq_fraction
    baseShifted i lambda reference mass hbase htarget

/-- Every finite Hermitian background inherits the oriented one-site count
interlacing for the frozen Anderson diagonal. -/
theorem problem_frozenAnderson_oneSite_thresholdCount
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) {lambda mass mass' : Real}
    (hlambda : 0 ≤ lambda) (hmass : mass ≤ mass') (E : Real) :
    orderedEigenvalueThresholdCount
        ⟨frozenOneSiteAndersonMatrix background i lambda mass',
          oneSiteAndersonMatrix_isHermitian background hbackground i
            (andersonDiagonalPotential lambda mass')⟩ E ≤
      orderedEigenvalueThresholdCount
        ⟨frozenOneSiteAndersonMatrix background i lambda mass,
          oneSiteAndersonMatrix_isHermitian background hbackground i
            (andersonDiagonalPotential lambda mass)⟩ E ∧
    orderedEigenvalueThresholdCount
        ⟨frozenOneSiteAndersonMatrix background i lambda mass,
          oneSiteAndersonMatrix_isHermitian background hbackground i
            (andersonDiagonalPotential lambda mass)⟩ E ≤
      orderedEigenvalueThresholdCount
        ⟨frozenOneSiteAndersonMatrix background i lambda mass',
          oneSiteAndersonMatrix_isHermitian background hbackground i
            (andersonDiagonalPotential lambda mass')⟩ E + 1 :=
  frozenOneSiteAndersonThresholdCount_sandwich
    background hbackground i hlambda hmass E

#print axioms problem_frozenAnderson_sharp_oneSite_density
#print axioms problem_frozenAnderson_oneSite_localGreen_fraction
#print axioms problem_frozenAnderson_oneSite_thresholdCount

end

end ArchonPhysicsConsumers.Thermalization.ProblemFrozenAndersonOneSiteSpectralAveraging
