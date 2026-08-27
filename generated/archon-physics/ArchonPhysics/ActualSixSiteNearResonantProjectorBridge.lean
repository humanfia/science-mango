import ArchonPhysics.ActualSixSiteNearResonantAdjugateBridge
import ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum
import ArchonPhysics.ActualProjectorAdjugateSpectralSystem

/-!
# Projector consumption of the six-site near-resonant adjugate witness

This module specializes the exact adjugate bridge to the physical mass path
and transfers determinant nondegeneracy to the genuine ordered-projector
minor used by the lifted frequency Jacobian.
-/

namespace ArchonPhysics.ActualSixSiteNearResonantProjectorBridge

open ArchonPhysics
open ArchonPhysics.ActualProjectorAdjugatePolynomial
open ArchonPhysics.ActualProjectorAdjugateSpectralSystem
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantAdjugateBridge
open ArchonPhysics.ActualSixSiteNearResonantAdjugateFactor
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedProjectorShiftedAdjugate
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

/-- The three selected genuine dual energies at an actual six-site triple. -/
def actualSixSiteSelectedDualEnergy
    (modes : Fin 3 → Fin 6) (triple : MassTriple) : Fin 3 → Real :=
  fun r ↦ orderedEigenvalue
    (actualThreeMassDualHermitian frozenUnitMassSix
      (0 : Lattice.Site 6) (1 : Lattice.Site 6)
      (2 : Lattice.Site 6) triple)
    (modes r)

/-- Any actual triple whose inverse coordinates lie on the displayed path has
the displayed shifted-adjugate weight matrix. -/
theorem orderedShiftedAdjugateWeightMatrix_eq_nearResonant
    (t : Real) (modes : Fin 3 → Fin 6) (triple : MassTriple)
    (hcoordinates :
      inverseMassCoordinates
          (threeMassSiteConfig frozenUnitMassSix
            (0 : Lattice.Site 6) (1 : Lattice.Site 6)
            (2 : Lattice.Site 6) triple) =
        sixSiteNearResonantInverseWeights t)
    (hminus : t - 1 ≠ 0) (hplus : t + 1 ≠ 0) :
    orderedShiftedAdjugateWeightMatrix
        (actualThreeMassDualHermitian frozenUnitMassSix
          (0 : Lattice.Site 6) (1 : Lattice.Site 6)
          (2 : Lattice.Site 6) triple)
        modes
        (actualThreeMassCycleDirection
          (0 : Lattice.Site 6) (1 : Lattice.Site 6)
          (2 : Lattice.Site 6)) =
      nearResonantAdjugateWeightMatrix t
        (actualSixSiteSelectedDualEnergy modes triple) := by
  rw [← parameterAdjugateWeightMatrix_sixSiteNearResonant_eq_displayed
    t (actualSixSiteSelectedDualEnergy modes triple) hminus hplus]
  have hbase := weightedCycleLaplacian_actualThreeMass_eq_matrixVal
    frozenUnitMassSix (0 : Lattice.Site 6) (1 : Lattice.Site 6)
      (2 : Lattice.Site 6) triple
  rw [hcoordinates] at hbase
  ext r s
  simp only [orderedShiftedAdjugateWeightMatrix,
    parameterAdjugateWeightMatrix, orderedEigenvalueShiftedMatrix,
    parameterShiftedMatrix, actualSixSiteSelectedDualEnergy]
  rw [hbase]

/-- On a simple actual triple on the path, projector-minor degeneracy is
exactly degeneracy of the displayed three-column adjugate matrix. -/
theorem actualThreeMassProjectorMinor_eq_zero_iff_nearResonantAdjugate
    (t : Real) (modes : Fin 3 → Fin 6) (triple : MassTriple)
    (hcoordinates :
      inverseMassCoordinates
          (threeMassSiteConfig frozenUnitMassSix
            (0 : Lattice.Site 6) (1 : Lattice.Site 6)
            (2 : Lattice.Site 6) triple) =
        sixSiteNearResonantInverseWeights t)
    (hsimple : SimpleOrderedSpectrum
      (actualThreeMassDualHermitian frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6)
        (2 : Lattice.Site 6) triple))
    (hminus : t - 1 ≠ 0) (hplus : t + 1 ≠ 0) :
    (actualThreeMassProjectorWeightMatrix frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6)
        (2 : Lattice.Site 6) modes triple).det = 0 ↔
      (nearResonantAdjugateWeightMatrix t
        (actualSixSiteSelectedDualEnergy modes triple)).det = 0 := by
  rw [actualThreeMassProjectorMinor_eq_zero_iff_shiftedAdjugate
    frozenUnitMassSix (0 : Lattice.Site 6) (1 : Lattice.Site 6)
      (2 : Lattice.Site 6) modes triple hsimple]
  rw [orderedShiftedAdjugateWeightMatrix_eq_nearResonant
    t modes triple hcoordinates hminus hplus]

/-- Nondegeneracy transfers in the direction needed by the Jacobian
consumer. -/
theorem actualThreeMassProjectorMinor_ne_zero_of_nearResonantAdjugate
    (t : Real) (modes : Fin 3 → Fin 6) (triple : MassTriple)
    (hcoordinates :
      inverseMassCoordinates
          (threeMassSiteConfig frozenUnitMassSix
            (0 : Lattice.Site 6) (1 : Lattice.Site 6)
            (2 : Lattice.Site 6) triple) =
        sixSiteNearResonantInverseWeights t)
    (hsimple : SimpleOrderedSpectrum
      (actualThreeMassDualHermitian frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6)
        (2 : Lattice.Site 6) triple))
    (hminus : t - 1 ≠ 0) (hplus : t + 1 ≠ 0)
    (hdisplayed :
      (nearResonantAdjugateWeightMatrix t
        (actualSixSiteSelectedDualEnergy modes triple)).det ≠ 0) :
    (actualThreeMassProjectorWeightMatrix frozenUnitMassSix
      (0 : Lattice.Site 6) (1 : Lattice.Site 6)
      (2 : Lattice.Site 6) modes triple).det ≠ 0 := by
  intro hzero
  apply hdisplayed
  exact (actualThreeMassProjectorMinor_eq_zero_iff_nearResonantAdjugate
    t modes triple hcoordinates hsimple hminus hplus).mp hzero

/-- The physical raw-mass path has exactly the inverse coordinates used by
the algebraic bridge. -/
theorem inverseMassCoordinates_nearResonantMassTriple
    {t : Real} (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport) :
    inverseMassCoordinates
        (threeMassSiteConfig frozenUnitMassSix
          (0 : Lattice.Site 6) (1 : Lattice.Site 6)
          (2 : Lattice.Site 6) (nearResonantMassTriple t)) =
      sixSiteNearResonantInverseWeights t := by
  change inverseMassCoordinates
      (actualSixSiteThreeMassConfig (nearResonantMassTriple t)) = _
  rw [inverseMassCoordinates_actualSixSiteThreeMassConfig hsupport,
    sixSiteSliceInverseWeights_nearResonantMassTriple]
  rfl

/-- Fully specialized physical-path zero-set equivalence, with primal simple
spectrum converted to dual simple spectrum internally. -/
theorem actualSixSitePath_projectorMinor_eq_zero_iff_nearResonantAdjugate
    {t : Real} (modes : Fin 3 → Fin 6)
    (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)))
    (hminus : t - 1 ≠ 0) (hplus : t + 1 ≠ 0) :
    (actualThreeMassProjectorWeightMatrix frozenUnitMassSix
        (0 : Lattice.Site 6) (1 : Lattice.Site 6)
        (2 : Lattice.Site 6) modes (nearResonantMassTriple t)).det = 0 ↔
      (nearResonantAdjugateWeightMatrix t
        (actualSixSiteSelectedDualEnergy modes
          (nearResonantMassTriple t))).det = 0 := by
  apply actualThreeMassProjectorMinor_eq_zero_iff_nearResonantAdjugate
  · exact inverseMassCoordinates_nearResonantMassTriple hsupport
  · apply simple_actualThreeMassDualHermitian_of_simple
    simpa [actualSixSiteThreeMassHarmonic] using hsimple
  · exact hminus
  · exact hplus


/-- Specialized nondegeneracy transfer on the physical path. -/
theorem actualSixSitePath_projectorMinor_ne_zero_of_nearResonantAdjugate
    {t : Real} (modes : Fin 3 → Fin 6)
    (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)))
    (hminus : t - 1 ≠ 0) (hplus : t + 1 ≠ 0)
    (hdisplayed :
      (nearResonantAdjugateWeightMatrix t
        (actualSixSiteSelectedDualEnergy modes
          (nearResonantMassTriple t))).det ≠ 0) :
    (actualThreeMassProjectorWeightMatrix frozenUnitMassSix
      (0 : Lattice.Site 6) (1 : Lattice.Site 6)
      (2 : Lattice.Site 6) modes (nearResonantMassTriple t)).det ≠ 0 := by
  intro hzero
  apply hdisplayed
  exact (actualSixSitePath_projectorMinor_eq_zero_iff_nearResonantAdjugate
    modes hsupport hsimple hminus hplus).mp hzero
end

end ArchonPhysics.ActualSixSiteNearResonantProjectorBridge
