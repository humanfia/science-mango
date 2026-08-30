import ArchonPhysics.ActualEightSiteFullIIDLocalLinearSmallBallUpper
import ArchonPhysics.QuantitativeSmallBallAtlasClosure

/-!
# Actual full-eight regular points and pointwise small-ball charts

This module separates the certified witness used by the first full-eight
small-ball theorem from the local analytic argument.  A regular point records
exactly the physical support, simple-spectrum, positive-mode, and nonzero
selected-Jacobian conditions.  At every such point the actual augmented
spectral map has an invertible strict derivative and hence a local linear
small-ball upper bound.

No claim is made here that the regular set has full iid measure.  That is the
remaining global nondegeneracy obligation.
-/

open scoped ENNReal Matrix Topology ContDiff

namespace ArchonPhysics.ActualEightSiteFullIIDRegularLocalSmallBallUpper

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteFullIIDAugmentedSpectralChart
open ArchonPhysics.ActualEightSiteFullIIDLocalLinearSmallBallUpper
open ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.ActualEightSiteFullJointSpectralDifferentiability
open ArchonPhysics.ActualLiftedMismatchSmallBall
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.HarmonicModes
open ArchonPhysics.LocalParametricJacobianSmallBallPipeline
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ParametricLiftedMismatchSmallBall
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.SelectedFirstPartialJacobianChart
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Function MeasureTheory Set

noncomputable section

/-- The true selected three-mass slice Jacobian at an actual eight-mass
configuration. -/
def actualEightSiteSelectedPartialJacobian
    (x : EightMassVector) : MassTriple →L[Real] MassTriple :=
  actualThreeMassLiftedFrequencyJacobian (fullEightMassConfig x)
    (actualEightSiteSelectedSites 0)
    (actualEightSiteSelectedSites 1)
    (actualEightSiteSelectedSites 2)
    actualEightSiteDecaySign actualEightSiteDecayModes
    (splitEightMass x).2

/-- The transparent regular locus for the selected full-eight chart.  The
positive-mode clause is retained explicitly even though it follows for the
currently selected physical modes on the support interior. -/
def fullEightSelectedJacobianRegularSet : Set EightMassVector :=
  {x | x ∈ fullEightMassSupportInterior ∧
    SimpleOrderedSpectrum (fullEightHarmonic x) ∧
    (∀ r : Fin 3,
      0 < orderedEigenvalue (fullEightHarmonic x)
        (actualEightSiteDecayModes r)) ∧
    (actualEightSiteSelectedPartialJacobian x).det ≠ 0}

theorem mem_fullEightSelectedJacobianRegularSet_iff
    (x : EightMassVector) :
    x ∈ fullEightSelectedJacobianRegularSet ↔
      x ∈ fullEightMassSupportInterior ∧
      SimpleOrderedSpectrum (fullEightHarmonic x) ∧
      (∀ r : Fin 3,
        0 < orderedEigenvalue (fullEightHarmonic x)
          (actualEightSiteDecayModes r)) ∧
      (actualEightSiteSelectedPartialJacobian x).det ≠ 0 := by
  rfl

/-- At every regular point, the selected partial derivative of the actual
full-eight lifted family is invertible.  This is the arbitrary-point version
of the earlier certified-witness construction. -/
theorem exists_fullEightLiftedFamily_strictDerivative_partial_isInvertible_of_regular
    {x : EightMassVector} (hx : x ∈ fullEightSelectedJacobianRegularSet) :
    ∃ derivative :
        (EightMassEnvironment × MassTriple) →L[Real] MassTriple,
      HasStrictFDerivAt fullEightLiftedFamily derivative
          (splitEightMass x) ∧
        (derivative ∘L ContinuousLinearMap.inr Real
          EightMassEnvironment MassTriple).IsInvertible := by
  rcases hx with ⟨hxSupport, hsimple, _hpositive, hJacobian⟩
  obtain ⟨Dfull, hDfull⟩ :=
    exists_hasStrictFDerivAt_actualEightSiteFullLiftedFrequencyChart
      hxSupport hsimple
  let derivative :
      (EightMassEnvironment × MassTriple) →L[Real] MassTriple :=
    Dfull ∘L splitEightMass.symm.toContinuousLinearMap
  have hfamily : HasStrictFDerivAt fullEightLiftedFamily derivative
      (splitEightMass x) := by
    have hDfullAt : HasStrictFDerivAt
        actualEightSiteFullLiftedFrequencyChart Dfull
          (splitEightMass.symm (splitEightMass x)) := by
      simpa using hDfull
    change HasStrictFDerivAt
      (fun p => actualEightSiteFullLiftedFrequencyChart
        (splitEightMass.symm p)) derivative (splitEightMass x)
    simpa [derivative, Function.comp_def] using
      hDfullAt.comp (splitEightMass x)
        splitEightMass.symm.hasStrictFDerivAt
  let partialDerivative : MassTriple →L[Real] MassTriple :=
    derivative ∘L ContinuousLinearMap.inr Real
      EightMassEnvironment MassTriple
  have hsliceRaw := hfamily.hasFDerivAt.comp (splitEightMass x).2
    (hasFDerivAt_prodMk_right (splitEightMass x).1
      (splitEightMass x).2)
  have hslice : HasFDerivAt
      (fun triple : MassTriple =>
        fullEightLiftedFamily ((splitEightMass x).1, triple))
      partialDerivative (splitEightMass x).2 := by
    change HasFDerivAt
      (fun triple : MassTriple =>
        fullEightLiftedFamily ((splitEightMass x).1, triple))
      partialDerivative (splitEightMass x).2 at hsliceRaw
    simpa [partialDerivative] using hsliceRaw
  have hsliceThree : HasFDerivAt
      (actualThreeMassLiftedFrequencyChart (fullEightMassConfig x)
        (actualEightSiteSelectedSites 0)
        (actualEightSiteSelectedSites 1)
        (actualEightSiteSelectedSites 2)
        actualEightSiteDecaySign actualEightSiteDecayModes)
      partialDerivative (splitEightMass x).2 := by
    simpa only [fullEightLiftedFamily_fixed_environment hxSupport] using hslice
  have hJacobianPartial : actualEightSiteSelectedPartialJacobian x =
      partialDerivative := by
    simpa [actualEightSiteSelectedPartialJacobian,
      actualThreeMassLiftedFrequencyJacobian] using hsliceThree.fderiv
  have hpartialDet : partialDerivative.det ≠ 0 := by
    rw [← hJacobianPartial]
    exact hJacobian
  have hpartialInvertible : partialDerivative.IsInvertible := by
    let partialEquiv :=
      partialDerivative.toContinuousLinearEquivOfDetNeZero hpartialDet
    exact ⟨partialEquiv,
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero
        partialDerivative hpartialDet⟩
  exact ⟨derivative, hfamily, hpartialInvertible⟩

end

end ArchonPhysics.ActualEightSiteFullIIDRegularLocalSmallBallUpper
