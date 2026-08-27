import ArchonPhysics.ActualSixSiteNearResonantModularCertificate
import Mathlib.LinearAlgebra.Matrix.Kronecker

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate

open ArchonPhysics.ActualSixSiteNearResonantModularCertificate

/-- The fixed `t = 1/10` companion matrix over `ZMod 103`. -/
def companion103 : Matrix (Fin 5) (Fin 5) (ZMod 103) :=
  !![0, 0, 0, 0, 27;
     1, 0, 0, 0, 23;
     0, 1, 0, 0, 89;
     0, 0, 1, 0, 83;
     0, 0, 0, 1, 11]

/-- The first five powers send the origin column to the corresponding basis column. -/
theorem companion103_pow_column_origin :
    ∀ a i : Fin 5,
      (companion103 ^ a.val) i 0 =
        (1 : Matrix (Fin 5) (Fin 5) (ZMod 103)) i a := by
  decide

/-- The first nine origin columns agree with the reduced-power table. -/
theorem companion103_pow_column_eq_reducedPower :
    ∀ n : Fin 9, ∀ i : Fin 5,
      (companion103 ^ n.val) i 0 = reducedPower103 n i := by
  decide

end ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate
