import Family6Grounding.Family6CanonicalFrostmanConstantCoreV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family6CanonicalFrostmanUnitAmbientBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6CanonicalFrostmanConstantCoreV1

noncomputable section

universe u

/-- For a family contained in a unit-volume ambient body, the canonical
Frostman constant is exactly maximal concentration divided by the full indexed
family volume. -/
theorem canonicalFrostmanConstant_eq_maximalConcentration_div_familyVolume
    {index : Type u} [Fintype index]
    (F : ConvexFamily index) (K : ConvexBody Space)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (K : Set Space))
    (hunit : volume (K : Set Space) = 1) :
    canonicalFrostmanConstant F K =
      maximalConcentration F / familyVolume F := by
  unfold canonicalFrostmanConstant
  rw [containedMass_eq_familyVolume_of_contained F K hcontained, hunit]
  simp

/-- With positive finite family volume, a canonical Frostman bound is
equivalent to the exact maximal-concentration-times-family-volume budget. -/
theorem canonicalFrostmanConstant_le_iff_maximalConcentration_le_mul_familyVolume
    {index : Type u} [Fintype index]
    (F : ConvexFamily index) (K : ConvexBody Space)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (K : Set Space))
    (hunit : volume (K : Set Space) = 1)
    (hvolume0 : familyVolume F ≠ 0)
    (hvolumeTop : familyVolume F ≠ ∞)
    (C : ENNReal) :
    canonicalFrostmanConstant F K ≤ C ↔
      maximalConcentration F ≤ C * familyVolume F := by
  rw [canonicalFrostmanConstant_eq_maximalConcentration_div_familyVolume
    F K hcontained hunit]
  exact ENNReal.div_le_iff hvolume0 hvolumeTop

theorem maximalConcentration_le_mul_familyVolume_of_canonicalFrostmanConstant_le
    {index : Type u} [Fintype index]
    (F : ConvexFamily index) (K : ConvexBody Space)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (K : Set Space))
    (hunit : volume (K : Set Space) = 1)
    (hvolume0 : familyVolume F ≠ 0)
    (hvolumeTop : familyVolume F ≠ ∞)
    (C : ENNReal)
    (hFrostman : canonicalFrostmanConstant F K ≤ C) :
    maximalConcentration F ≤ C * familyVolume F :=
  (canonicalFrostmanConstant_le_iff_maximalConcentration_le_mul_familyVolume
    F K hcontained hunit hvolume0 hvolumeTop C).mp hFrostman

#print axioms canonicalFrostmanConstant_eq_maximalConcentration_div_familyVolume
#print axioms canonicalFrostmanConstant_le_iff_maximalConcentration_le_mul_familyVolume
#print axioms maximalConcentration_le_mul_familyVolume_of_canonicalFrostmanConstant_le

end
end Family6CanonicalFrostmanUnitAmbientBridgeV1
