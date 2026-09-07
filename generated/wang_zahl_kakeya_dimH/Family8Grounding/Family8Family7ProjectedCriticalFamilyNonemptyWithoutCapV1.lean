import FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
import FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
import Mathlib.Tactic

/-!
# Projected critical-family nonemptiness without a near-fibre cap

The canonical coefficient selection is a maximal separated subfamily of a
finite active tube image.  Its `code` already supplies a selected member for
each source member.  Consequently nonemptiness needs only one active index;
the stronger local near-fibre cap and three-member estimate are unnecessary
for the norm-scale selector's nonemptiness premise.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set
open scoped NNReal

namespace Family8Family7ProjectedCriticalFamilyNonemptyWithoutCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1

noncomputable section

universe u v

/-- A nonempty finite tube family has a nonempty canonical maximal separated
selection, directly through the selection code. -/
theorem selectedTubes_nonempty_of_family_nonempty
    {radius : NNReal} (family : Finset (Tube radius)) (scale : Real)
    (hfamily : family.Nonempty) :
    (selectedTubes family scale).Nonempty := by
  classical
  obtain ⟨T, hT⟩ := hfamily
  let member : TubeMember family := ⟨T, hT⟩
  let center := coefficientCode family scale member
  refine ⟨center.1.1, ?_⟩
  rw [selectedTubes, Finset.mem_image]
  exact ⟨center.1, center.2, rfl⟩

/-- One active index already gives one selected projected critical tube. -/
theorem actualProjectedCriticalFamily_nonempty_of_active_nonempty
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (active : Finset iota)
    (hactive : active.Nonempty) :
    (actualProjectedCriticalFamily fine active).Nonempty := by
  apply selectedTubes_nonempty_of_family_nonempty
  obtain ⟨i, hi⟩ := hactive
  refine ⟨fine.tubes i, ?_⟩
  exact (mem_activeTubeImage_iff fine active (fine.tubes i)).mpr
    ⟨i, hi, rfl⟩

/-- A positive lower multiplicity endpoint makes every actual normalized
critical family on that band nonempty, with no pairwise or cap hypothesis. -/
theorem actualProjectedAmbientCriticalFamily_nonempty_on_multiplicityBand_of_lower_pos
    {point : Type v} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading point iota)
    {lower upper : Nat} (hlowerPos : 0 < lower) :
    ∀ x, x ∈ physical.multiplicityBand lower upper →
      (actualProjectedAmbientCriticalFamily fine physical.ambient
        (physical.activeAtPoint x)).Nonempty := by
  intro x hx
  rw [actualProjectedAmbientCriticalFamily_eq_activeAtPoint fine physical x]
  apply actualProjectedCriticalFamily_nonempty_of_active_nonempty
  apply Finset.card_pos.mp
  exact hlowerPos.trans_le (physical.mem_multiplicityBand.mp hx).2.1

#print axioms selectedTubes_nonempty_of_family_nonempty
#print axioms actualProjectedCriticalFamily_nonempty_of_active_nonempty
#print axioms
  actualProjectedAmbientCriticalFamily_nonempty_on_multiplicityBand_of_lower_pos

end
end Family8Family7ProjectedCriticalFamilyNonemptyWithoutCapV1
