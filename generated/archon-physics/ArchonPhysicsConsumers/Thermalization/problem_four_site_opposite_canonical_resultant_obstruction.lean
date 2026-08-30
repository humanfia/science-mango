import ArchonPhysics.FourSiteOppositeCanonicalResultantObstruction

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
open ArchonPhysics.FourSiteOppositeCanonicalResultantObstruction

noncomputable section

/-- The counterexample uses a genuinely positive frozen background. -/
example (site : Lattice.Site 4) : 0 < unitMassFour.mass site :=
  unitMassFour.mass_pos site

/-- The two varied sites in the counterexample are distinct. -/
example : (0 : Lattice.Site 4) ≠ 2 := by norm_num +decide

/-- Nevertheless, the canonical vertical characteristic resultant vanishes
identically. -/
example :
    twoSitePositiveCharacteristicJacobianResultant unitMassFour
      (0 : Lattice.Site 4) (2 : Lattice.Site 4) = 0 :=
  opposite_positiveCharacteristicJacobianResultant_eq_zero

end

end ArchonPhysicsConsumers.Thermalization
