import Family8Grounding.Family8OwnerFiberKatzTaoFromAmbientFrostmanV2
import Family6Grounding.Family6CanonicalFrostmanConstantCoreV1
import Mathlib.Tactic

/-!
# Canonical ambient density from the actual family volume

For a family which is Frostman inside an ambient convex body, all members are
already contained in that body.  Hence its ambient contained mass is exactly
its indexed family volume.  When the ambient volume is nonzero and finite,
the literal quotient `familyVolume / volume ambient` supplies the base
normalization needed to upgrade ambient Frostman control to a global
Katz--Tao estimate.  No ambient-mass comparison callback is required.

V1 omitted the namespace exporting the contained-mass identity and is not
imported.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8AmbientFamilyVolumeDensityV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6CanonicalFrostmanConstantCoreV1
open Family8OwnerFiberKatzTaoFromAmbientFrostmanV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true

universe u

/-- The actual indexed family mass divided by the actual ambient volume. -/
def ambientFamilyVolumeDensity
    {iota : Type u} [Fintype iota]
    (F : ConvexFamily iota) (ambient : ConvexBody Space) : ENNReal :=
  familyVolume F / volume (ambient : Set Space)

/-- The canonical ambient density is finite whenever the ambient has
positive volume. -/
theorem ambientFamilyVolumeDensity_ne_top
    {iota : Type u} [Fintype iota]
    (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hvolume0 : volume (ambient : Set Space) ≠ 0) :
    ambientFamilyVolumeDensity F ambient ≠ ∞ := by
  unfold ambientFamilyVolumeDensity
  exact ENNReal.div_ne_top (familyVolume_lt_top F).ne hvolume0

/-- The quotient gives the exact ambient contained-mass normalization for a
family genuinely contained in the ambient body. -/
theorem containedMass_eq_ambientFamilyVolumeDensity_mul
    {iota : Type u} [Fintype iota]
    (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (ambient : Set Space))
    (hvolume0 : volume (ambient : Set Space) ≠ 0)
    (hvolumeTop : volume (ambient : Set Space) ≠ ∞) :
    containedMass F ambient =
      ambientFamilyVolumeDensity F ambient *
        volume (ambient : Set Space) := by
  rw [containedMass_eq_familyVolume_of_contained F ambient hcontained]
  unfold ambientFamilyVolumeDensity
  exact (ENNReal.div_mul_cancel hvolume0 hvolumeTop).symm

/-- Ambient Frostman control upgrades to global Katz--Tao with the literal
actual family-volume density. -/
theorem isKatzTao_of_isFrostmanIn_familyVolumeDensity
    {iota : Type u} [Fintype iota]
    {F : ConvexFamily iota} {ambient : ConvexBody Space} {CF : ENNReal}
    (hF : IsFrostmanIn CF F ambient)
    (hvolume0 : volume (ambient : Set Space) ≠ 0)
    (hvolumeTop : volume (ambient : Set Space) ≠ ∞) :
    IsKatzTao (CF * ambientFamilyVolumeDensity F ambient) F := by
  apply isKatzTao_of_isFrostmanIn_of_ambientMass hF
  rw [containedMass_eq_ambientFamilyVolumeDensity_mul F ambient
    hF.family_subset hvolume0 hvolumeTop]

#print axioms ambientFamilyVolumeDensity_ne_top
#print axioms containedMass_eq_ambientFamilyVolumeDensity_mul
#print axioms isKatzTao_of_isFrostmanIn_familyVolumeDensity

end

end Family8AmbientFamilyVolumeDensityV2
