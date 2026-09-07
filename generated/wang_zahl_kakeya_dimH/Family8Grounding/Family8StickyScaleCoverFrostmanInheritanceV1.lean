import Family8Grounding.Family8FrostmanInheritanceToActiveCoarseV3
import Family8Grounding.Family8StickyParentHullVolumeBoundV1

/-!
# Upward Frostman inheritance for an actual Sticky scale cover

A `StickyScaleCover` already supplies the finite active index sets, parent
map, and literal fine-to-coarse tube containment required by a
`ConvexFactorization`.  This file exposes that factorization and specializes
the generic upward Frostman theorem to its actual assigned fibre masses.

`UniformTubeFamily` contains no ambient-support or admissibility field.  The
arbitrary-ambient theorem therefore states coarse containment explicitly.  A
second theorem derives that premise for the canonical radius-four ambient
body from an admissible `ActualTubeDatum` and `rho <= 1`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyScaleCoverFrostmanInheritanceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyParentHullVolumeBoundV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The literal geometric factorization carried by a Sticky scale cover.
No new analytic field is introduced: the active sets, parent map, and
containment proof are copied directly from the cover. -/
def toConvexFactorization (S : StickyScaleCover fine rho) :
    ConvexFactorization fine.bodyFamily S.coarse.bodyFamily where
  index :=
    { fine := S.activeFine
      coarse := S.activeCoarse
      parent := S.parent
      parent_mem := S.parent_mem }
  contained := by
    intro i hi
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using
      S.carrier_subset i hi

@[simp] theorem toConvexFactorization_fine
    (S : StickyScaleCover fine rho) :
    (toConvexFactorization S).index.fine = S.activeFine := by
  rfl

@[simp] theorem toConvexFactorization_coarse
    (S : StickyScaleCover fine rho) :
    (toConvexFactorization S).index.coarse = S.activeCoarse := by
  rfl

@[simp] theorem toConvexFactorization_parent
    (S : StickyScaleCover fine rho) (i : iota) :
    (toConvexFactorization S).index.parent i = S.parent i := by
  rfl

@[simp] theorem toConvexFactorization_fiber
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) :
    (toConvexFactorization S).index.fiber k = S.fiber k := by
  rfl

/-- The factorization's assigned body mass is definitionally the sum over the
actual Sticky fibre. -/
theorem toConvexFactorization_fiberBodyMass
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) :
    fiberBodyMass (toConvexFactorization S) k =
      ∑ i ∈ S.fiber k, volume (fine.bodyFamily i : Set Space) := by
  rfl

/-- Upward Frostman inheritance on an actual Sticky scale cover.

The only analytic inputs are the fine Frostman certificate and the two-sided
comparison between each actual assigned fibre mass and its coarse tube
volume.  Since `UniformTubeFamily` has no ambient-support field, containment
of the active coarse tubes in `K` is the minimal additional geometric input. -/
theorem activeCoarse_isFrostmanOn_of_comparable_fiberDensity
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    {C lower upper : ENNReal}
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfine : IsFrostmanOn C fine.bodyFamily S.activeFine K)
    (hcoarseContained : ∀ k ∈ S.activeCoarse,
      (S.coarse.bodyFamily k : Set Space) ⊆ (K : Set Space))
    (hlower : ∀ k ∈ S.activeCoarse,
      lower * volume (S.coarse.bodyFamily k : Set Space) ≤
        fiberBodyMass (toConvexFactorization S) k)
    (hupper : ∀ k ∈ S.activeCoarse,
      fiberBodyMass (toConvexFactorization S) k ≤
        upper * volume (S.coarse.bodyFamily k : Set Space)) :
    IsFrostmanOn (C * upper * lower⁻¹)
      S.coarse.bodyFamily S.activeCoarse K := by
  exact
    _root_.Family8FrostmanInheritanceToActiveCoarseV3.activeCoarse_isFrostmanOn_of_comparable_fiberDensity
        (toConvexFactorization S) K hlower0 hlowerTop hfine
        hcoarseContained hlower hupper

/-- For an admissible actual tube datum, the existing Sticky parent geometry
supplies the ambient-containment premise in the radius-four body. -/
theorem activeCoarse_isFrostmanOn_closedBallFour_of_admissible
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrhoOne : rho ≤ 1)
    {C lower upper : ENNReal}
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfine : IsFrostmanOn C D.family.bodyFamily S.activeFine
      closedBallFourBody)
    (hlower : ∀ k ∈ S.activeCoarse,
      lower * volume (S.coarse.bodyFamily k : Set Space) ≤
        fiberBodyMass (toConvexFactorization S) k)
    (hupper : ∀ k ∈ S.activeCoarse,
      fiberBodyMass (toConvexFactorization S) k ≤
        upper * volume (S.coarse.bodyFamily k : Set Space)) :
    IsFrostmanOn (C * upper * lower⁻¹)
      S.coarse.bodyFamily S.activeCoarse closedBallFourBody := by
  apply activeCoarse_isFrostmanOn_of_comparable_fiberDensity
    S closedBallFourBody hlower0 hlowerTop hfine
  · intro k hk
    let kk : {k // k ∈ S.activeCoarse} := ⟨k, hk⟩
    have hparent :=
      _root_.Family8StickyParentHullVolumeBoundV1.activeCoarseFamily_body_subset_closedBall_four
          D hD S hrhoOne kk
    simpa only [FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily,
      UniformTubeFamily.bodyFamily, Tube.coe_body, coe_closedBallFourBody]
      using hparent
  · exact hlower
  · exact hupper

#print axioms toConvexFactorization_fine
#print axioms toConvexFactorization_coarse
#print axioms toConvexFactorization_parent
#print axioms toConvexFactorization_fiber
#print axioms toConvexFactorization_fiberBodyMass
#print axioms activeCoarse_isFrostmanOn_of_comparable_fiberDensity
#print axioms
  activeCoarse_isFrostmanOn_closedBallFour_of_admissible

end StickyScaleCover

end

end Family8StickyScaleCoverFrostmanInheritanceV1
