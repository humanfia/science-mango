import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import Family8Grounding.Family8SelectedParentJohnPlankSideWidthBridgeV5
import Mathlib.Tactic

/-!
# Thickened-plank control under a common affine image

Euclidean closed thickenings are not invariant under an arbitrary affine
equivalence.  Accordingly the generic transport theorem below asks only for
the exact pullback implication that its proof uses.  A second theorem proves
that implication for a positive scalar dilation, with the sharp scale
conditions on the transverse width and aspect ratio.

Neither theorem changes the thick-control parameter `M` or reselects any
family member.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8PlankThickControlAffineImageTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]

private theorem scalarDilation_preimage_cthickening_subset
    {s r : NNReal} (hs : 0 < s) {A B : Set Space} (hB : IsCompact B)
    (h : scalarDilationAffineEquiv s hs '' A ⊆
      Metric.cthickening (r : Real)
        (scalarDilationAffineEquiv s hs '' B)) :
    A ⊆ Metric.cthickening (((r / s : NNReal) : Real)) B := by
  let d := scalarDilationAffineEquiv s hs
  intro x hx
  have hdx : d x ∈ Metric.cthickening (r : Real) (d '' B) :=
    h ⟨x, hx, rfl⟩
  have hdCompact : IsCompact (d '' B) :=
    hB.image d.continuous_of_finiteDimensional
  rw [hdCompact.cthickening_eq_biUnion_closedBall (by positivity)] at hdx
  simp only [mem_iUnion, Metric.mem_closedBall] at hdx
  obtain ⟨y, hyImage, hdist⟩ := hdx
  obtain ⟨z, hz, rfl⟩ := hyImage
  apply Metric.mem_cthickening_of_dist_le x z
    (((r / s : NNReal) : Real)) B hz
  have hsReal : (0 : Real) < (s : Real) := by exact_mod_cast hs
  have hscaled : (s : Real) * dist x z ≤ (r : Real) := by
    simpa only [d, scalarDilationAffineEquiv_apply, dist_smul₀,
      Real.norm_eq_abs, abs_of_pos hsReal] using hdist
  rw [NNReal.coe_div]
  exact (le_div_iff₀ hsReal).2 (by simpa [mul_comm] using hscaled)

/-- Thickened-plank control transports without loss once target thickening
containment is known to pull back to the source thickening at the same
admissible `theta`.  The aspect-ratio inequality is exactly what lets a
target-admissible `theta` enter the source control. -/
theorem frostmanThickenedPlankControl_affineImage_of_pullback
    {aSource bSource aTarget bTarget M : NNReal}
    (e : Space ≃ᵃ[Real] Space)
    (Dsource : ShadedConvexPlankFamily iota aSource bSource)
    (Dtarget : ShadedConvexPlankFamily iota aTarget bTarget)
    (hfamily : Dtarget.family = affineImageFamily e Dsource.family)
    (haspect : aSource / bSource ≤ aTarget / bTarget)
    (hpullback : forall theta,
      aTarget / bTarget ≤ theta -> theta ≤ 1 -> forall i j,
      (affineImageConvexBody e (Dsource.family j) : Set Space) ⊆
          Metric.cthickening
            (((theta * bTarget : NNReal) : Real))
            (affineImageConvexBody e (Dsource.family i) : Set Space) ->
        (Dsource.family j : Set Space) ⊆
          Metric.cthickening
            (((theta * bSource : NNReal) : Real))
            (Dsource.family i : Set Space))
    (hcontrol : FrostmanThickenedPlankControl Dsource M) :
    FrostmanThickenedPlankControl Dtarget M := by
  refine ⟨hcontrol.1, ?_⟩
  intro theta hthetaLower hthetaUpper i
  have hsource := hcontrol.2 theta
    (haspect.trans hthetaLower) hthetaUpper i
  have hsubset : thickenedPlankIndices Dtarget theta i ⊆
      thickenedPlankIndices Dsource theta i := by
    intro j hj
    rw [thickenedPlankIndices,
      Family6AffinePlankAnalyticHypothesesStableV1.containedIndices] at hj ⊢
    have hjContained := (Finset.mem_filter.mp hj).2
    rw [hfamily] at hjContained
    have hjImage :
        (affineImageConvexBody e (Dsource.family j) : Set Space) ⊆
          Metric.cthickening
            (((theta * bTarget : NNReal) : Real))
            (affineImageConvexBody e (Dsource.family i) : Set Space) := by
      simpa only [affineImageFamily_apply] using hjContained
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ j,
        hpullback theta hthetaLower hthetaUpper i j hjImage⟩
  have hcard : (thickenedPlankIndices Dtarget theta i).card ≤
      (thickenedPlankIndices Dsource theta i).card :=
    Finset.card_le_card hsubset
  exact (by exact_mod_cast hcard :
    ((thickenedPlankIndices Dtarget theta i).card : ENNReal) ≤
      ((thickenedPlankIndices Dsource theta i).card : ENNReal)).trans hsource

/-- Positive common scalar dilation preserves thickened-plank control with
the same `M`, provided the target width pulls back below the source width and
the target admissible aspect interval is contained in the source interval. -/
theorem frostmanThickenedPlankControl_scalarDilation
    {aSource bSource aTarget bTarget s M : NNReal}
    (hs : 0 < s)
    (Dsource : ShadedConvexPlankFamily iota aSource bSource)
    (Dtarget : ShadedConvexPlankFamily iota aTarget bTarget)
    (hfamily : Dtarget.family =
      affineImageFamily (scalarDilationAffineEquiv s hs) Dsource.family)
    (haspect : aSource / bSource ≤ aTarget / bTarget)
    (hwidth : bTarget / s ≤ bSource)
    (hcontrol : FrostmanThickenedPlankControl Dsource M) :
    FrostmanThickenedPlankControl Dtarget M := by
  apply frostmanThickenedPlankControl_affineImage_of_pullback
    (scalarDilationAffineEquiv s hs) Dsource Dtarget hfamily haspect
  · intro theta _ _ i j hj
    have himage :
        scalarDilationAffineEquiv s hs '' (Dsource.family j : Set Space) ⊆
          Metric.cthickening
            (((theta * bTarget : NNReal) : Real))
            (scalarDilationAffineEquiv s hs ''
              (Dsource.family i : Set Space)) := by
      simpa only [coe_affineImageConvexBody] using hj
    have hpull := scalarDilation_preimage_cthickening_subset
      hs (Dsource.family i).isCompact himage
    have hradius : (theta * bTarget) / s ≤ theta * bSource := by
      calc
        (theta * bTarget) / s = theta * (bTarget / s) := by
          exact mul_div_assoc theta bTarget s
        _ ≤ theta * bSource := by
          gcongr
    exact hpull.trans
      (Metric.cthickening_mono (by exact_mod_cast hradius)
        (Dsource.family i : Set Space))
  · exact hcontrol

#print axioms frostmanThickenedPlankControl_affineImage_of_pullback
#print axioms frostmanThickenedPlankControl_scalarDilation

end

end Family8PlankThickControlAffineImageTransportV1
