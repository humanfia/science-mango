import Submission.Kakeya.ConvexFactoring.GreedyLateTailRestart
import Family8Grounding.Family8RestrictedActualDatumMassBridgeV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SharpKatzTaoOrGreedyHighConcentrationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumMassBridgeV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

/-!
# Honest sharp Katz--Tao versus actual greedy concentration

This is the callback-free first step of the concentration dichotomy.  It does
not infer a sharp Katz--Tao estimate from Frostman hypotheses.  If the sharp
estimate fails, the full finite-hull maximizer supplies an actual nonempty
fiber in an actual convex hull whose density is strictly larger than the
requested coefficient.  The restricted datum remains admissible and its
selected family is genuinely constant-one Frostman in that winning hull.

The first two lemmas record exact transport to any genuine finite restriction.
They will also be used by the first-low-density tail split: a factor-two mass
retention inequality automatically gives the same factor-two comparison of
average multiplicities.
-/

/-- Any explicit shading-mass retention bound transports average multiplicity
to the genuine restricted datum.  The denominator inequality is automatic
because the restricted shaded union is a subset of the source union. -/
theorem source_averageMultiplicity_le_loss_mul_restrictActualTubeDatum
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (selected : Finset index)
    (loss : ENNReal)
    (hmass : D.shading.shadingMass <=
      loss * (restrictActualTubeDatum D selected).shading.shadingMass) :
    D.shading.averageMultiplicity <=
      loss * (restrictActualTubeDatum D selected).shading.averageMultiplicity := by
  let restricted := restrictActualTubeDatum D selected
  have hunion : restricted.shading.shadedUnion <=
      D.shading.shadedUnion :=
    restrictActualTubeDatum_shadedUnion_subset D selected
  unfold Shading.averageMultiplicity
  calc
    D.shading.shadingMass / volume D.shading.shadedUnion <=
        (loss * restricted.shading.shadingMass) /
          volume D.shading.shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ <= (loss * restricted.shading.shadingMass) /
          volume restricted.shading.shadedUnion :=
      ENNReal.div_le_div_left (measure_mono hunion) _
    _ = loss *
          (restricted.shading.shadingMass /
            volume restricted.shading.shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Active Katz--Tao control becomes ordinary Katz--Tao control on the exact
subtype-indexed restriction. -/
theorem isKatzTao_restrictActualTubeDatum_of_isKatzTaoOn
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (selected : Finset index)
    (A : ENNReal) (hKT : IsKatzTaoOn A D.family.bodyFamily selected) :
    IsKatzTao A (restrictActualTubeDatum D selected).family.bodyFamily := by
  intro K
  unfold IsKatzTaoAt
  rw [restrictActualTubeDatum_containedMass]
  exact hKT K

/-- Active Frostman control becomes ordinary Frostman control on the exact
subtype-indexed restriction. -/
theorem isFrostmanIn_restrictActualTubeDatum_of_isFrostmanOn
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (selected : Finset index)
    (K : ConvexBody Space) (C : ENNReal)
    (hF : IsFrostmanOn C D.family.bodyFamily selected K) :
    IsFrostmanIn C
      (restrictActualTubeDatum D selected).family.bodyFamily K := by
  refine And.intro ?_ ?_
  · intro i
    exact hF.1 i.1 i.2
  · intro Kprime hKprime
    rw [restrictActualTubeDatum_containedMass,
      restrictActualTubeDatum_containedMass]
    exact hF.2 Kprime hKprime

/-- Honest central alternative at one requested coefficient.  The negative
branch contains an actual high-concentration convex hull and actual restricted
datum; no Katz--Tao or desired-RHS callback is introduced. -/
theorem isKatzTao_or_exists_actual_highConcentration_frostmanRestriction
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    [Nonempty index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible) (A : ENNReal) :
    IsKatzTao A D.family.bodyFamily ∨
      ∃ M : MaximalDensityChoice D.family.bodyFamily Finset.univ
          (hullCandidates (Finset.univ : Finset index))
          (hullContainer D.family.bodyFamily),
        M.fiber.Nonempty ∧
        A < densityInside D.family.bodyFamily Finset.univ
          (hullContainer D.family.bodyFamily M.index) ∧
        (restrictActualTubeDatum D M.fiber).IsAdmissible ∧
        IsFrostmanIn 1
          (restrictActualTubeDatum D M.fiber).family.bodyFamily
          (hullContainer D.family.bodyFamily M.index) := by
  classical
  by_cases hKT : IsKatzTao A D.family.bodyFamily
  · exact Or.inl hKT
  · right
    have hactive : (Finset.univ : Finset index).Nonempty :=
      Finset.univ_nonempty
    obtain ⟨M, hMfiber⟩ :=
      exists_maximalDensityChoice_fiber_nonempty D.family.bodyFamily
        (Finset.univ : Finset index) (hullCandidates (Finset.univ : Finset index))
        (hullContainer D.family.bodyFamily) hactive
        (fun i hi => hullCandidates_cover D.family.bodyFamily hi)
    have hnotAll : ¬ (∀ K : ConvexBody Space,
        concentration D.family.bodyFamily K <= A) := by
      intro hAll
      exact hKT (isKatzTao_iff_concentration_le.mpr hAll)
    push Not at hnotAll
    obtain ⟨K, hK⟩ := hnotAll
    have hKdensity : A < densityInside D.family.bodyFamily Finset.univ K := by
      simpa [densityInside, massInside, concentration, indicesInside,
        containedIndices] using hK
    have hmax : densityInside D.family.bodyFamily Finset.univ K <=
        densityInside D.family.bodyFamily Finset.univ
          (hullContainer D.family.bodyFamily M.index) :=
      maximalDensityChoice_density_ge_all M hactive (fun _ hi => hi) K
    have hOn : IsFrostmanOn 1 D.family.bodyFamily M.fiber
        (hullContainer D.family.bodyFamily M.index) :=
      hullChoice_fiber_isFrostmanOn_one M hactive (fun _ hi => hi)
    exact ⟨M, hMfiber, hKdensity.trans_le hmax,
      Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
        hD M.fiber,
      isFrostmanIn_restrictActualTubeDatum_of_isFrostmanOn
        D M.fiber (hullContainer D.family.bodyFamily M.index) 1 hOn⟩

#print axioms source_averageMultiplicity_le_loss_mul_restrictActualTubeDatum
#print axioms isKatzTao_restrictActualTubeDatum_of_isKatzTaoOn
#print axioms isFrostmanIn_restrictActualTubeDatum_of_isFrostmanOn
#print axioms isKatzTao_or_exists_actual_highConcentration_frostmanRestriction

end
end Family8SharpKatzTaoOrGreedyHighConcentrationV1
