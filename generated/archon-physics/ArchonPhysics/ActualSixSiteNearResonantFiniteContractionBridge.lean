import ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra
import ArchonPhysics.ActualSixSiteNearResonantJacobianCompleteWitness

/-!
# Finite-coordinate form of the six-site dual-adjugate contraction

This module transports the physical edge-space contraction to the literal
`Fin 6` shifted matrices used by symbolic elimination.  It separates the
spectral/topological witness from the eventual polynomial or quotient-ring
certificate.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantFiniteContractionBridge

open ArchonPhysics
open ArchonPhysics.ActualProjectorAdjugateSpectralSystem
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantAdjugateBridge
open ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum
open ArchonPhysics.ActualSixSiteNearResonantProjectorBridge
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.HarmonicModes
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedProjectorShiftedAdjugate
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

noncomputable section

/-- Literal `Fin 6` triple contraction at arbitrary spectral parameters. -/
def sixSiteNearResonantFiniteAdjugateInteractionContraction
    (t : Real) (energy : Fin 3 → Real) : Real :=
  adjugateEntryProductContraction
    (fun r ↦ sixSiteNearResonantFinShiftedMatrix t energy r)

/-- On the supported physical path, the abstract dual-adjugate interaction
contraction is exactly its literal finite-coordinate expression. -/
theorem harmonicDualOrderedAdjugateInteractionContraction_eq_finite
    {t : Real} (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport) :
    harmonicDualOrderedAdjugateInteractionContraction
        (actualSixSiteThreeMassConfig (nearResonantMassTriple t))
        cleanSixSiteDecayModes =
      sixSiteNearResonantFiniteAdjugateInteractionContraction t
        (actualSixSiteSelectedDualEnergy cleanSixSiteDecayModes
          (nearResonantMassTriple t)) := by
  let mass := actualSixSiteThreeMassConfig (nearResonantMassTriple t)
  let dual := dualMassWeightedHarmonicHermitian mass
  let energy := actualSixSiteSelectedDualEnergy cleanSixSiteDecayModes
    (nearResonantMassTriple t)
  let family : Fin 3 → Matrix (Lattice.Site 6) (Lattice.Site 6) Real :=
    fun r ↦ orderedEigenvalueShiftedMatrix dual (cleanSixSiteDecayModes r)
  have hcoordinates : inverseMassCoordinates mass =
      sixSiteNearResonantInverseWeights t := by
    simpa [mass, actualSixSiteThreeMassConfig] using
      inverseMassCoordinates_nearResonantMassTriple hsupport
  have hbase :
      Matrix.reindex (siteEquivFin 6) (siteEquivFin 6) (matrixVal dual) =
        sixSiteNearResonantFinLaplacian t := by
    have hphysical := weightedCycleLaplacian_actualThreeMass_eq_matrixVal
      frozenUnitMassSix (0 : Lattice.Site 6) (1 : Lattice.Site 6)
        (2 : Lattice.Site 6) (nearResonantMassTriple t)
    change weightedCycleLaplacian
        (weightsOfCoordinates (inverseMassCoordinates mass)) =
      matrixVal dual at hphysical
    rw [hcoordinates] at hphysical
    calc
      Matrix.reindex (siteEquivFin 6) (siteEquivFin 6) (matrixVal dual) =
          Matrix.reindex (siteEquivFin 6) (siteEquivFin 6)
            (weightedCycleLaplacian
              (weightsOfCoordinates (sixSiteNearResonantInverseWeights t))) :=
        congrArg (Matrix.reindex (siteEquivFin 6) (siteEquivFin 6))
          hphysical.symm
      _ = finWeightedCycleLaplacian
          (sixSiteNearResonantInverseWeights t) := rfl
      _ = sixSiteNearResonantFinLaplacian t :=
        finWeightedCycleLaplacian_sixSiteNearResonantInverseWeights t
  have hfamily (r : Fin 3) :
      Matrix.reindex (siteEquivFin 6) (siteEquivFin 6) (family r) =
        sixSiteNearResonantFinShiftedMatrix t energy r := by
    ext i j
    simp only [family, orderedEigenvalueShiftedMatrix,
      sixSiteNearResonantFinShiftedMatrix, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply]
    have hbaseEntry := congrArg (fun M => M i j) hbase
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply] at hbaseEntry
    rw [hbaseEntry]
    by_cases hij : i = j
    · subst j
      simp [energy, actualSixSiteSelectedDualEnergy, dual, mass,
        actualSixSiteThreeMassConfig, actualThreeMassDualHermitian]
    · have hsymm :
          (siteEquivFin 6).symm i ≠ (siteEquivFin 6).symm j :=
        (siteEquivFin 6).symm.injective.ne hij
      simp [energy, actualSixSiteSelectedDualEnergy, dual, mass,
        actualSixSiteThreeMassConfig, actualThreeMassDualHermitian, hij, hsymm]
  change adjugateEntryProductContraction family =
    adjugateEntryProductContraction
      (fun r ↦ sixSiteNearResonantFinShiftedMatrix t energy r)
  rw [← adjugateEntryProductContraction_reindex
    (siteEquivFin 6) family]
  congr 1
  funext r
  exact hfamily r

end

end ArchonPhysics.ActualSixSiteNearResonantFiniteContractionBridge
