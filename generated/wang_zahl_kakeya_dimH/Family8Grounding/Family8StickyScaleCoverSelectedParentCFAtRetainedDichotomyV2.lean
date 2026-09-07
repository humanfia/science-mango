import Family8Grounding.Family8StickyScaleCoverSelectedParentCFAtDichotomyV1
import Family8Grounding.Family8StickyScaleCoverSelectedParentCFAtHullChoiceV2
import Family8Grounding.Family8StickyScaleCoverSelectedFiberAmbientMassRetentionV3
import Mathlib.Tactic

/-!
# The genuine high/low normalized-CF split at one retained parent, V2

The parent `q` is prescribed by the caller, so this package applies directly
to a mass-popular parent and never replaces it by a cover-wide CF maximizer.
The high branch carries an actual nonempty full-convex hull choice in that
same fibre.  The low branch carries an actual `IsFrostmanIn` certificate on
the literal card-retained selected subtype, with exact loss `16 * L`.  V1
used a universe-polymorphic index against the existing universe-zero
dichotomy and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyScaleCoverSelectedParentCFAtRetainedDichotomyV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8StickyScaleCoverSelectedParentCFAtDichotomyV1.StickyScaleCover
open Family8StickyScaleCoverSelectedParentCFAtHullChoiceV2
open Family8StickyScaleCoverSelectedParentCFAtHullChoiceV2.SelectedParentCFAtHullChoice
open Family8StickyScaleCoverSelectedFiberAmbientMassRetentionV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- At one prescribed active parent, a lower CF barrier gives either its
literal high-density hull witness or a Frostman certificate on the caller's
literal card-retained selected subtype. -/
theorem exists_highHull_or_selected_isFrostmanIn
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    {lower L : ENNReal}
    (hcard : (Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) <=
      L * (selected.card : ENNReal)) :
    (∃ Q : SelectedParentCFAtHullChoice S q,
      lower * familyVolume (S.fiberFamily q.1) <=
        densityInside (S.fiberFamily q.1) Finset.univ Q.hull *
          volume (S.activeCoarseFamily q : Set Space)) ∨
      IsFrostmanIn (lower * (16 * L))
        (activeSubtypeFamily (S.fiberFamily q.1) selected)
        (S.activeCoarseFamily q) := by
  rcases lower_le_cfAt_or_isFrostmanIn S hdelta q lower with
    hHigh | hLow
  · left
    obtain ⟨Q⟩ := selectedParentCFAtHullChoice_nonempty S q
    exact ⟨Q,
      Q.lower_mul_fiberVolume_le_winnerDensity_mul_parentVolume
        hdelta hHigh⟩
  · right
    exact lowCF_isFrostmanIn_selected_of_card_retention
      S hdeltaHalf q selected hLow hcard

#print axioms exists_highHull_or_selected_isFrostmanIn

end
end Family8StickyScaleCoverSelectedParentCFAtRetainedDichotomyV2
