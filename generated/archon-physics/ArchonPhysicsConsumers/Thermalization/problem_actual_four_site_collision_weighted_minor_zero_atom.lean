import ArchonPhysics.ActualFourSiteCollisionWeightedMinorZeroAtom

open ArchonPhysics
open ArchonPhysics.ActualFourSiteCollisionWeightedMinorZeroAtom
open ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorBadPeak
open ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorZeroAtom
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter MeasureTheory Set

example :
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        frozenUnitMassFour (0 : Lattice.Site 4) (1 : Lattice.Site 4)
          (2 : Lattice.Site 4) ({0} : Set Real) = 0 :=
  actualFourSite_collisionWeightedProjectorMinorDistribution_singleton_zero

example :
    Tendsto
      (fun n : Nat =>
        actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel
          frozenUnitMassFour (0 : Lattice.Site 4) (1 : Lattice.Site 4)
            (2 : Lattice.Site 4) (1 / ((n : Real) + 1)))
      atTop (nhds 0) :=
  tendsto_actualFourSite_collisionWeightedProjectorMinorBadLevel_zero

#print axioms
  ArchonPhysics.ActualFourSiteCollisionWeightedMinorZeroAtom.actualFourSite_collisionWeightedProjectorMinorDistribution_singleton_zero
#print axioms
  ArchonPhysics.ActualFourSiteCollisionWeightedMinorZeroAtom.tendsto_actualFourSite_collisionWeightedProjectorMinorBadLevel_zero
