import Family8Grounding.Family8PlankCanonicalUnitSlabIncidenceV5
import Family6Grounding.Family6PlankSlabUniformVolumeConcentrationGammaOneV1
import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankCanonicalUnitSlabMemberCountV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6PlankSlabUniformVolumeConcentrationGammaOneV1
open Family8PlankCanonicalUnitSlabIncidenceV5

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Concrete member count for the canonical certified incidence

The comparison-certified plank volume gives a uniform positive lower volume
on every nonempty actual family.  Applying the existing contained-mass
argument to the derived canonical incidence bounds its literal member set;
no member-count or incidence conclusion is supplied as input.
-/

/-- The exact common lower volume furnished by the `IsPlank` certificates. -/
def certifiedPlankVolumeLower
    (D : ShadedConvexPlankFamily iota a b) : ENNReal :=
  ((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ (3 : Nat) *
    ((a : ENNReal) * (b : ENNReal))

/-- On a nonempty actual family, the certified lower volume is positive,
finite, and below every literal plank volume. -/
theorem certifiedPlank_uniformMemberVolumeLower
    (D : ShadedConvexPlankFamily iota a b) (hindex : Nonempty iota) :
    UniformMemberVolumeLower D (certifiedPlankVolumeLower D) := by
  let i0 : iota := Classical.choice hindex
  have ha : 0 < a := (D.all_isPlank i0).1
  have hab : a <= b := (D.all_isPlank i0).2.1
  have hb : 0 < b := ha.trans_le hab
  have hC : 0 < D.comparisonConstant :=
    zero_lt_one.trans_le (D.all_isPlank i0).2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · simp [certifiedPlankVolumeLower, hC.ne', ha.ne', hb.ne']
  · exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
  · intro i
    exact (D.all_isPlank i).volume_lower_bound

/-- Literal member-count times the certified member volume is controlled by
maximal concentration and the actual slab thickness. -/
theorem canonicalUnitSlab_members_card_mul_certifiedVolume_le
    (D : ShadedConvexPlankFamily iota a b) (hindex : Nonempty iota)
    (theta : NNReal) (S : ConvexBody Space) (hS : IsSlab 1 theta S) :
    ((((canonicalUnitSlabIncidence D hindex).toPlankSlabIncidence.members
        theta S).card : ENNReal) * certifiedPlankVolumeLower D) <=
      maximalConcentration D.family * (theta : ENNReal) := by
  exact members_card_mul_volumeLower_le
    (canonicalUnitSlabIncidence D hindex).toPlankSlabIncidence
    (certifiedPlank_uniformMemberVolumeLower D hindex) 1 theta S hS

/-- The sole remaining input for the scale-linear analytic count is the
explicit scalar comparison between maximal concentration and the certified
total member volume. -/
theorem canonicalUnitSlab_count_gamma_one
    (D : ShadedConvexPlankFamily iota a b) (hindex : Nonempty iota)
    (eta : Real)
    (hbudget : maximalConcentration D.family <=
      (a : ENNReal) ^ (-eta) * (Fintype.card iota : ENNReal) *
        certifiedPlankVolumeLower D) :
    forall theta : NNReal, a / b <= theta -> theta <= 1 ->
      forall S : ConvexBody Space, IsSlab 1 theta S ->
        ((((canonicalUnitSlabIncidence D hindex).toPlankSlabIncidence.members
          theta S).card : ENNReal) <=
            (a : ENNReal) ^ (-eta) * (theta : ENNReal) ^ (1 : Real) *
              (Fintype.card iota : ENNReal)) := by
  exact count_gamma_one_of_uniformVolume_maximalConcentration
    (canonicalUnitSlabIncidence D hindex).toPlankSlabIncidence
    (certifiedPlank_uniformMemberVolumeLower D hindex) 1 eta hbudget

/-- Callback-free canonical `gamma = 1` slab-incidence control. -/
theorem canonicalUnitSlab_katzTaoControl_gamma_one
    (D : ShadedConvexPlankFamily iota a b) (hindex : Nonempty iota)
    (eta : Real)
    (hbudget : maximalConcentration D.family <=
      (a : ENNReal) ^ (-eta) * (Fintype.card iota : ENNReal) *
        certifiedPlankVolumeLower D) :
    KatzTaoSlabIncidenceControl D
      (canonicalUnitSlabIncidence D hindex).toPlankSlabIncidence 1 eta 1 := by
  exact katzTaoControl_gamma_one_of_uniformVolume_maximalConcentration
    (canonicalUnitSlabIncidence D hindex).toPlankSlabIncidence
    (certifiedPlank_uniformMemberVolumeLower D hindex) 1 eta hbudget

#print axioms certifiedPlank_uniformMemberVolumeLower
#print axioms canonicalUnitSlab_members_card_mul_certifiedVolume_le
#print axioms canonicalUnitSlab_count_gamma_one
#print axioms canonicalUnitSlab_katzTaoControl_gamma_one

end
end Family8PlankCanonicalUnitSlabMemberCountV2
