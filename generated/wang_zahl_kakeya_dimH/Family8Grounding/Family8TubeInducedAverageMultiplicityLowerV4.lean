import Family8Grounding.Family8TubeFullNeighborhoodVolumeComparisonV8
import Submission.Kakeya.ConvexFactoring.StatisticLevelRestriction
import Submission.Kakeya.Uniformity.TubeFamily

/-!
# Average multiplicity lower bound for tube-induced neighborhoods, V4

V3 is frozen with misplaced scoped `omit` declarations.  This successor
keeps the corrected measure and division proofs and locally disables only
the unused-section-variable linter for the generic theorem interface.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal Pointwise InnerProductSpace
open MeasureTheory Set

namespace Family8TubeInducedAverageMultiplicityLowerV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8TubeFullNeighborhoodVolumeComparisonV8

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type*}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- Multiplicity of the full, untruncated parent-fibre neighborhoods. -/
noncomputable def fullNeighborhoodMultiplicity
    (P : ConvexFactorization fine.bodyFamily coarse.bodyFamily)
    (Y : Shading fine.bodyFamily) (x : Space) : Nat := by
  classical
  exact (Finset.univ.filter fun k ↦
    x ∈ Metric.thickening (rho : Real) (P.fiberShadedUnion Y k)).card

theorem fullNeighborhoodMultiplicity_cast_eq_sum_indicator
    (P : ConvexFactorization fine.bodyFamily coarse.bodyFamily)
    (Y : Shading fine.bodyFamily) (x : Space) :
    (fullNeighborhoodMultiplicity P Y x : ENNReal) =
      ∑ k, (Metric.thickening (rho : Real)
        (P.fiberShadedUnion Y k)).indicator
          (fun _ ↦ (1 : ENNReal)) x := by
  classical
  simp [fullNeighborhoodMultiplicity, Set.indicator_apply]

theorem lintegral_fullNeighborhoodMultiplicity
    (P : ConvexFactorization fine.bodyFamily coarse.bodyFamily)
    (Y : Shading fine.bodyFamily) :
    ∫⁻ x, (fullNeighborhoodMultiplicity P Y x : ENNReal) ∂volume =
      ∑ k, volume (Metric.thickening (rho : Real)
        (P.fiberShadedUnion Y k)) := by
  simp_rw [fullNeighborhoodMultiplicity_cast_eq_sum_indicator]
  rw [lintegral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro k _hk
    exact lintegral_indicator_one Metric.isOpen_thickening.measurableSet
  · intro k _hk
    exact measurable_const.indicator Metric.isOpen_thickening.measurableSet

/-- An exact outer count at every fine shaded point gives the same lower
count on the full `rho`-thickening of the fine shaded union. -/
theorem outerMultiplicity_le_fullNeighborhoodMultiplicity_on_thickening
    (P : ConvexFactorization fine.bodyFamily coarse.bodyFamily)
    (Y : Shading fine.bodyFamily) (m : Nat)
    (houter : ∀ x ∈ Y.shadedUnion, m ≤ P.outerMultiplicity Y x)
    (y : Space) (hy : y ∈ Metric.thickening (rho : Real) Y.shadedUnion) :
    m ≤ fullNeighborhoodMultiplicity P Y y := by
  obtain ⟨x, hxY, hyx⟩ := Metric.mem_thickening_iff.mp hy
  apply (houter x hxY).trans
  classical
  unfold ConvexFactorization.outerMultiplicity fullNeighborhoodMultiplicity
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨Finset.mem_univ k, ?_⟩
  obtain ⟨_hkCoarse, i, hiFiber, hxi⟩ :=
    (P.mem_inducedShading_carrier_iff Y k x).1 hk.2
  apply Metric.mem_thickening_iff.mpr
  exact ⟨x, Set.mem_iUnion.mpr ⟨⟨i, hiFiber⟩, hxi⟩, hyx⟩

/-- Integrated full-neighborhood multiplicity lower bound. -/
theorem natCast_mul_volume_thickening_le_sum_fullNeighborhoodVolumes
    (P : ConvexFactorization fine.bodyFamily coarse.bodyFamily)
    (Y : Shading fine.bodyFamily) (m : Nat)
    (houter : ∀ x ∈ Y.shadedUnion, m ≤ P.outerMultiplicity Y x) :
    (m : ENNReal) * volume
        (Metric.thickening (rho : Real) Y.shadedUnion) ≤
      ∑ k, volume (Metric.thickening (rho : Real)
        (P.fiberShadedUnion Y k)) := by
  rw [← lintegral_fullNeighborhoodMultiplicity P Y]
  calc
    (m : ENNReal) * volume
        (Metric.thickening (rho : Real) Y.shadedUnion) =
        ∫⁻ x, (Metric.thickening (rho : Real) Y.shadedUnion).indicator
          (fun _ ↦ (m : ENNReal)) x ∂volume := by
      rw [lintegral_indicator Metric.isOpen_thickening.measurableSet]
      simp
    _ ≤ ∫⁻ x, (fullNeighborhoodMultiplicity P Y x : ENNReal)
          ∂volume := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ Metric.thickening (rho : Real) Y.shadedUnion
      · simp only [Set.indicator_of_mem hx]
        exact_mod_cast
          outerMultiplicity_le_fullNeighborhoodMultiplicity_on_thickening
            P Y m houter x hx
      · simp [hx]

/-- Sum the per-parent full-to-truncated comparison on an actual uniform
coarse tube family. -/
theorem sum_fullNeighborhoodVolumes_le_twoHundredSixteen_mul_inducedMass
    (P : ConvexFactorization fine.bodyFamily coarse.bodyFamily)
    (Y : Shading fine.bodyFamily) (hrho : 0 < rho) :
    (∑ k, volume (Metric.thickening (rho : Real)
      (P.fiberShadedUnion Y k))) ≤
      216 * (P.neighborhoodInducedShading Y (rho : Real)).shadingMass := by
  calc
    (∑ k, volume (Metric.thickening (rho : Real)
        (P.fiberShadedUnion Y k))) ≤
        ∑ k, 216 * volume
          ((P.neighborhoodInducedShading Y (rho : Real)).carrier k) := by
      apply Finset.sum_le_sum
      intro k _hk
      have hsubset : P.fiberShadedUnion Y k ⊆
          (coarse.tubes k).carrier := by
        simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using
          P.fiberShadedUnion_subset_coarseBody Y k
      simpa [ConvexFactorization.neighborhoodInducedShading_carrier,
        UniformTubeFamily.bodyFamily, Tube.coe_body] using
        volume_thickening_le_twoHundredSixteen_mul_tube_inter_thickening
          (coarse.tubes k) hsubset hrho
    _ = 216 * ∑ k,
        volume ((P.neighborhoodInducedShading Y (rho : Real)).carrier k) := by
      rw [Finset.mul_sum]
    _ = 216 *
        (P.neighborhoodInducedShading Y (rho : Real)).shadingMass := by
      rfl

/-- The induced coarse shaded union lies in the full thickening of the fine
shaded union. -/
theorem neighborhoodShadedUnion_subset_thickening_shadedUnion
    (P : ConvexFactorization fine.bodyFamily coarse.bodyFamily)
    (Y : Shading fine.bodyFamily) :
    (P.neighborhoodInducedShading Y (rho : Real)).shadedUnion ⊆
      Metric.thickening (rho : Real) Y.shadedUnion := by
  intro x hx
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
  have hxThick : x ∈ Metric.thickening (rho : Real)
      (P.fiberShadedUnion Y k) := hxk.2
  apply Metric.thickening_subset_of_subset (rho : Real) _ hxThick
  intro y hy
  obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
  exact Set.mem_iUnion.mpr ⟨i.1, hyi⟩

/-- Division-free form of the tube-induced average lower bound. -/
theorem natCast_mul_inducedUnionVolume_le_twoHundredSixteen_mul_inducedMass
    (P : ConvexFactorization fine.bodyFamily coarse.bodyFamily)
    (Y : Shading fine.bodyFamily) (m : Nat) (hrho : 0 < rho)
    (houter : ∀ x ∈ Y.shadedUnion, m ≤ P.outerMultiplicity Y x) :
    (m : ENNReal) * volume
        (P.neighborhoodInducedShading Y (rho : Real)).shadedUnion ≤
      216 * (P.neighborhoodInducedShading Y (rho : Real)).shadingMass := by
  calc
    (m : ENNReal) * volume
        (P.neighborhoodInducedShading Y (rho : Real)).shadedUnion ≤
        (m : ENNReal) * volume
          (Metric.thickening (rho : Real) Y.shadedUnion) :=
      mul_le_mul' le_rfl
        (measure_mono (neighborhoodShadedUnion_subset_thickening_shadedUnion
          P Y))
    _ ≤ ∑ k, volume (Metric.thickening (rho : Real)
          (P.fiberShadedUnion Y k)) :=
      natCast_mul_volume_thickening_le_sum_fullNeighborhoodVolumes
        P Y m houter
    _ ≤ 216 *
        (P.neighborhoodInducedShading Y (rho : Real)).shadingMass :=
      sum_fullNeighborhoodVolumes_le_twoHundredSixteen_mul_inducedMass
        P Y hrho

/-- Paper-style average conclusion.  Positive fine mass and active-fine
support make the induced union denominator nonzero; compact tube support
makes it finite. -/
theorem natCast_le_twoHundredSixteen_mul_inducedAverage
    (P : ConvexFactorization fine.bodyFamily coarse.bodyFamily)
    (Y : Shading fine.bodyFamily) (m : Nat) (hrho : 0 < rho)
    (hmass : Y.shadingMass ≠ 0)
    (hactive : Y.shadedUnion ⊆ P.activeFineShadedUnion Y)
    (houter : ∀ x ∈ Y.shadedUnion, m ≤ P.outerMultiplicity Y x) :
    (m : ENNReal) ≤ 216 *
      (P.neighborhoodInducedShading Y (rho : Real)).averageMultiplicity := by
  let Z := P.neighborhoodInducedShading Y (rho : Real)
  have hYsubsetZ : Y.shadedUnion ⊆ Z.shadedUnion :=
    hactive.trans
      (P.activeFineShadedUnion_subset_neighborhoodShadedUnion Y hrho)
  have hvolume0 : volume Z.shadedUnion ≠ 0 := by
    intro hzero
    apply hmass
    have hcarrier : ∀ i, volume (Y.carrier i) = 0 := by
      intro i
      have hle : volume (Y.carrier i) ≤ volume Z.shadedUnion := by
        exact MeasureTheory.measure_mono (μ := volume) (by
          intro x hx
          exact hYsubsetZ (Set.mem_iUnion.mpr ⟨i, hx⟩))
      exact nonpos_iff_eq_zero.mp (by simpa [hzero] using hle)
    unfold Shading.shadingMass
    simp [hcarrier]
  have hvolumeTop : volume Z.shadedUnion ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono Z.shadedUnion_subset_familyUnion).trans_lt
      ((volume_familyUnion_le coarse.bodyFamily).trans_lt
        (familyVolume_lt_top coarse.bodyFamily))
  unfold Shading.averageMultiplicity
  change (m : ENNReal) ≤ 216 * (Z.shadingMass / volume Z.shadedUnion)
  rw [← mul_div_assoc]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hvolume0) (Or.inl hvolumeTop)).2
  simpa only [Z] using
    natCast_mul_inducedUnionVolume_le_twoHundredSixteen_mul_inducedMass
      P Y m hrho houter

#print axioms fullNeighborhoodMultiplicity
#print axioms lintegral_fullNeighborhoodMultiplicity
#print axioms
  outerMultiplicity_le_fullNeighborhoodMultiplicity_on_thickening
#print axioms
  sum_fullNeighborhoodVolumes_le_twoHundredSixteen_mul_inducedMass
#print axioms natCast_le_twoHundredSixteen_mul_inducedAverage

end
end Family8TubeInducedAverageMultiplicityLowerV4
