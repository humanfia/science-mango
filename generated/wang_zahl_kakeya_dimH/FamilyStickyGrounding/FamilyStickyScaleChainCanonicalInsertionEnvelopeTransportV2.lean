import FamilyStickyGrounding.FamilyStickyScaleChainLocalSuccessorAssemblerV2
import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainCanonicalInsertionEnvelopeTransportV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.BoundedMonotoneRadiusChain
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
open FamilyStickyScaleChainHierarchyGlobalEnvelopeV2
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2
open FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence
open FamilyStickyScaleChainLocalSuccessorAssemblerV2
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence

noncomputable section

/-!
# Canonical envelope transport across one inserted scale

The generic recursive state stores an arbitrary `BufferedChainFamily`; it has
no field identifying that family with the coherent hierarchy selected by the
current scale sequence.  Consequently endpoint transport alone cannot imply
an envelope comparison for an arbitrary state.  This module records the
honest canonical specialization and proves the missing comparisons there.

The lower and upper children may use newly supplied initial bodies.  Every
other interval keeps the old initial body through `lowerChild.succAbove`.
Endpoint transport then identifies its depth-one radius chain, and hence its
coherent cover, hierarchy, canonical tube minimum, test bodies, and complete
hierarchy envelope.  No unchanged-envelope equality is assumed.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Initial bodies under insertion -/

/-- Insert two child bodies at the split interval.  The lower child is the
omitted `succAbove` coordinate; among old coordinates, the selected one is
replaced by the upper child and every other one is literally retained. -/
def insertedInitialBody {depth : Nat} (m : Fin depth)
    (oldBody : Fin depth -> ConvexBody Space)
    (upperBody lowerBody : ConvexBody Space) :
    Fin (depth + 1) -> ConvexBody Space :=
  fun k => Fin.succAboveCases (lowerChildIndex m) lowerBody
    (fun j => if j = m then upperBody else oldBody j) k

@[simp] theorem insertedInitialBody_lowerChild {depth : Nat}
    (m : Fin depth) (oldBody : Fin depth -> ConvexBody Space)
    (upperBody lowerBody : ConvexBody Space) :
    insertedInitialBody m oldBody upperBody lowerBody (lowerChildIndex m) =
      lowerBody := by
  simp [insertedInitialBody]

@[simp] theorem insertedInitialBody_succAbove {depth : Nat}
    (m j : Fin depth) (oldBody : Fin depth -> ConvexBody Space)
    (upperBody lowerBody : ConvexBody Space) :
    insertedInitialBody m oldBody upperBody lowerBody
        ((lowerChildIndex m).succAbove j) =
      if j = m then upperBody else oldBody j := by
  simp [insertedInitialBody]

@[simp] theorem insertedInitialBody_upperChild {depth : Nat}
    (m : Fin depth) (oldBody : Fin depth -> ConvexBody Space)
    (upperBody lowerBody : ConvexBody Space) :
    insertedInitialBody m oldBody upperBody lowerBody (upperChildIndex m) =
      upperBody := by
  have h := insertedInitialBody_succAbove m m oldBody upperBody lowerBody
  rw [lowerChild_succAbove_eq_upper] at h
  simpa using h

theorem insertedInitialBody_before {depth : Nat}
    (m j : Fin depth) (hjm : j < m)
    (oldBody : Fin depth -> ConvexBody Space)
    (upperBody lowerBody : ConvexBody Space) :
    insertedInitialBody m oldBody upperBody lowerBody
        (beforeIntervalEmbedding depth j) = oldBody j := by
  rw [<- lowerChild_succAbove_eq_before m j hjm]
  simp [ne_of_lt hjm]

theorem insertedInitialBody_after {depth : Nat}
    (m j : Fin depth) (hmj : m < j)
    (oldBody : Fin depth -> ConvexBody Space)
    (upperBody lowerBody : ConvexBody Space) :
    insertedInitialBody m oldBody upperBody lowerBody
        (afterIntervalEmbedding depth j) = oldBody j := by
  rw [<- lowerChild_succAbove_eq_after m j hmj]
  simp [ne_of_gt hmj]

/-- Positive volume is preserved by the body insertion once it is known for
the old bodies and the two new children. -/
theorem insertedInitialBody_volume_pos {depth : Nat}
    (m : Fin depth) (oldBody : Fin depth -> ConvexBody Space)
    (upperBody lowerBody : ConvexBody Space)
    (oldVolume_pos : forall j, 0 < volume (oldBody j : Set Space))
    (upperVolume_pos : 0 < volume (upperBody : Set Space))
    (lowerVolume_pos : 0 < volume (lowerBody : Set Space)) :
    forall k, 0 < volume
      (insertedInitialBody m oldBody upperBody lowerBody k : Set Space) := by
  intro k
  refine Fin.succAboveCases
    (α := fun k : Fin (depth + 1) =>
      0 < volume
        (insertedInitialBody m oldBody upperBody lowerBody k : Set Space))
    (lowerChildIndex m) (by simpa) ?_ k
  intro j
  by_cases hj : j = m
  · subst j
    simpa only [insertedInitialBody_succAbove, if_pos] using upperVolume_pos
  · simpa only [insertedInitialBody_succAbove, if_neg hj] using oldVolume_pos j

/-! ## Endpoint-determined depth-one chains -/

theorem BoundedMonotoneRadiusChain.eq_of_radius_eq
    {depth : Nat} (R₁ R₂ : BoundedMonotoneRadiusChain delta depth)
    (h : R₁.radius = R₂.radius) : R₁ = R₂ := by
  cases R₁
  cases R₂
  simp_all

/-- A canonical adjacent depth-one radius chain is determined by its two
endpoints.  All remaining structure fields are propositions. -/
theorem ofAdjacentInterval_eq_of_endpoints
    {depth₁ depth₂ : Nat}
    (S₁ : FiniteScaleSequence delta depth₁) (j₁ : Fin depth₁)
    (S₂ : FiniteScaleSequence delta depth₂) (j₂ : Fin depth₂)
    (htau : S₁.tau j₁ = S₂.tau j₂)
    (htheta : S₁.theta j₁ = S₂.theta j₂) :
    ofAdjacentInterval S₁ j₁ = ofAdjacentInterval S₂ j₂ := by
  apply BoundedMonotoneRadiusChain.eq_of_radius_eq
  funext q
  fin_cases q
  · exact htau
  · exact htheta

/-! ## Canonical quantities depend only on the transported interval -/

/-- The transparent canonical envelope of one chain, packaged as a scalar
function so equality of dependent hierarchy inputs can be transported by
ordinary congruence. -/
def canonicalOneStepChainEnvelope
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (R : BoundedMonotoneRadiusChain delta 1)
    (body : ConvexBody Space) : ENNReal :=
  (∏ l ∈ Finset.range 1,
    exactDimensionalLoss (R.toHierarchy C hfine) (by omega) body l *
      (if hl : l < 1 then
        (((R.intervalCover C l hl).activeFine.card : Nat) : ENNReal)
      else 1)) *
    ((volume (canonicalTestBody (R.toHierarchy C hfine) body 1 : Set Space) /
        volume (body : Set Space)) *
      (canonicalTubeVolume (R.toHierarchy C hfine) (by omega) 0 /
        canonicalTubeVolume (R.toHierarchy C hfine) (by omega) 1))

/-- The terminal concentration of one canonical chain, similarly packaged
to hide its dependent radius and cardinality indices. -/
def canonicalOneStepChainTerminal
    (C : CoherentStickyMultiscaleCover fine)
    (hfine : fine.refinement.refined.Nonempty)
    (R : BoundedMonotoneRadiusChain delta 1)
    (body : ConvexBody Space) : ENNReal :=
  concentration (effectiveActiveFamily (R.toHierarchy C hfine) 1)
    (canonicalTestBody (R.toHierarchy C hfine) body 1)

/-- The complete canonical hierarchy envelope is unchanged when the two
adjacent endpoints and the initial body are unchanged.  This unfolds through
the coherent cover, hierarchy, finite tube minimum, and recursive test body;
no envelope comparison is supplied to the theorem. -/
theorem canonicalHierarchyEnvelopeAt_eq_of_endpoints
    {depth₁ depth₂ : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (S₁ : FiniteScaleSequence delta depth₁) (j₁ : Fin depth₁)
    (S₂ : FiniteScaleSequence delta depth₂) (j₂ : Fin depth₂)
    (hfine : fine.refinement.refined.Nonempty)
    (body₁ : Fin depth₁ -> ConvexBody Space)
    (body₂ : Fin depth₂ -> ConvexBody Space)
    (htau : S₁.tau j₁ = S₂.tau j₂)
    (htheta : S₁.theta j₁ = S₂.theta j₂)
    (hbody : body₁ j₁ = body₂ j₂) :
    canonicalHierarchyEnvelopeAt
        (CoherentExactHierarchyFamily.ofFiniteScaleSequence C S₁ hfine)
        (by omega) body₁ j₁ =
      canonicalHierarchyEnvelopeAt
        (CoherentExactHierarchyFamily.ofFiniteScaleSequence C S₂ hfine)
        (by omega) body₂ j₂ := by
  have hchain := ofAdjacentInterval_eq_of_endpoints S₁ j₁ S₂ j₂
    htau htheta
  change canonicalOneStepChainEnvelope C hfine
      (ofAdjacentInterval S₁ j₁) (body₁ j₁) =
    canonicalOneStepChainEnvelope C hfine
      (ofAdjacentInterval S₂ j₂) (body₂ j₂)
  rw [hchain, hbody]

/-- The terminal concentration used by the canonical test-body producer is
also invariant under the same endpoint/body transport. -/
theorem canonicalTerminalConcentration_eq_of_endpoints
    {depth₁ depth₂ : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (S₁ : FiniteScaleSequence delta depth₁) (j₁ : Fin depth₁)
    (S₂ : FiniteScaleSequence delta depth₂) (j₂ : Fin depth₂)
    (hfine : fine.refinement.refined.Nonempty)
    (body₁ : Fin depth₁ -> ConvexBody Space)
    (body₂ : Fin depth₂ -> ConvexBody Space)
    (htau : S₁.tau j₁ = S₂.tau j₂)
    (htheta : S₁.theta j₁ = S₂.theta j₂)
    (hbody : body₁ j₁ = body₂ j₂) :
    let F₁ := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S₁ hfine
    let F₂ := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S₂ hfine
    concentration (effectiveActiveFamily (F₁.hierarchy j₁) 1)
        (canonicalTestBody (F₁.hierarchy j₁) (body₁ j₁) 1) =
      concentration (effectiveActiveFamily (F₂.hierarchy j₂) 1)
        (canonicalTestBody (F₂.hierarchy j₂) (body₂ j₂) 1) := by
  dsimp only
  have hchain := ofAdjacentInterval_eq_of_endpoints S₁ j₁ S₂ j₂
    htau htheta
  change canonicalOneStepChainTerminal C hfine
      (ofAdjacentInterval S₁ j₁) (body₁ j₁) =
    canonicalOneStepChainTerminal C hfine
      (ofAdjacentInterval S₂ j₂) (body₂ j₂)
  rw [hchain, hbody]

/-- The preceding transparent identity lifts to the generic hierarchy
envelope of the two canonical buffered families.  Volume-positivity and
terminal-normalization proofs affect only proof fields and therefore do not
appear in the resulting value. -/
theorem hierarchyGlobalEnvelopeAt_canonicalOneStep_eq_of_endpoints
    {depth₁ depth₂ : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (S₁ : FiniteScaleSequence delta depth₁) (j₁ : Fin depth₁)
    (S₂ : FiniteScaleSequence delta depth₂) (j₂ : Fin depth₂)
    (hfine : fine.refinement.refined.Nonempty) (delta_pos : 0 < delta)
    (body₁ : Fin depth₁ -> ConvexBody Space)
    (body₂ : Fin depth₂ -> ConvexBody Space)
    (volume_pos₁ : forall k, 0 < volume (body₁ k : Set Space))
    (volume_pos₂ : forall k, 0 < volume (body₂ k : Set Space))
    (terminal₁ : forall k,
      let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S₁ hfine
      concentration (effectiveActiveFamily (F.hierarchy k) 1)
          (canonicalTestBody (F.hierarchy k) (body₁ k) 1) <= 1)
    (terminal₂ : forall k,
      let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S₂ hfine
      concentration (effectiveActiveFamily (F.hierarchy k) 1)
          (canonicalTestBody (F.hierarchy k) (body₂ k) 1) <= 1)
    (htau : S₁.tau j₁ = S₂.tau j₂)
    (htheta : S₁.theta j₁ = S₂.theta j₂)
    (hbody : body₁ j₁ = body₂ j₂) :
    hierarchyGlobalEnvelopeAt
        (canonicalOneStepBufferedChainFamily C S₁ hfine delta_pos body₁
          volume_pos₁ terminal₁) j₁ =
      hierarchyGlobalEnvelopeAt
        (canonicalOneStepBufferedChainFamily C S₂ hfine delta_pos body₂
          volume_pos₂ terminal₂) j₂ := by
  change hierarchyGlobalEnvelopeAt
      (canonicalBufferedChainFamily
        (CoherentExactHierarchyFamily.ofFiniteScaleSequence C S₁ hfine)
        (by omega) delta_pos body₁ volume_pos₁ terminal₁) j₁ =
    hierarchyGlobalEnvelopeAt
      (canonicalBufferedChainFamily
        (CoherentExactHierarchyFamily.ofFiniteScaleSequence C S₂ hfine)
        (by omega) delta_pos body₂ volume_pos₂ terminal₂) j₂
  rw [hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_eq,
    hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_eq]
  exact canonicalHierarchyEnvelopeAt_eq_of_endpoints C S₁ j₁ S₂ j₂ hfine
    body₁ body₂ htau htheta hbody

/-! ## Specialization to the exact insertion coordinates -/

theorem canonicalHierarchyEnvelopeAt_before_eq
    {depth : Nat} (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (m j : Fin depth) (rho : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1))
    (href : ScaleSequenceRefinesAt S m rho S') (hjm : j < m)
    (hfine : fine.refinement.refined.Nonempty)
    (oldBody : Fin depth -> ConvexBody Space)
    (upperBody lowerBody : ConvexBody Space) :
    canonicalHierarchyEnvelopeAt
        (CoherentExactHierarchyFamily.ofFiniteScaleSequence C S' hfine)
        (by omega) (insertedInitialBody m oldBody upperBody lowerBody)
        (beforeIntervalEmbedding depth j) =
      canonicalHierarchyEnvelopeAt
        (CoherentExactHierarchyFamily.ofFiniteScaleSequence C S hfine)
        (by omega) oldBody j := by
  exact canonicalHierarchyEnvelopeAt_eq_of_endpoints C S'
    (beforeIntervalEmbedding depth j) S j hfine
    (insertedInitialBody m oldBody upperBody lowerBody) oldBody
    (tau_before_eq href hjm) (theta_before_eq href hjm)
    (insertedInitialBody_before m j hjm oldBody upperBody lowerBody)

theorem canonicalHierarchyEnvelopeAt_after_eq
    {depth : Nat} (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (m j : Fin depth) (rho : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1))
    (href : ScaleSequenceRefinesAt S m rho S') (hmj : m < j)
    (hfine : fine.refinement.refined.Nonempty)
    (oldBody : Fin depth -> ConvexBody Space)
    (upperBody lowerBody : ConvexBody Space) :
    canonicalHierarchyEnvelopeAt
        (CoherentExactHierarchyFamily.ofFiniteScaleSequence C S' hfine)
        (by omega) (insertedInitialBody m oldBody upperBody lowerBody)
        (afterIntervalEmbedding depth j) =
      canonicalHierarchyEnvelopeAt
        (CoherentExactHierarchyFamily.ofFiniteScaleSequence C S hfine)
        (by omega) oldBody j := by
  exact canonicalHierarchyEnvelopeAt_eq_of_endpoints C S'
    (afterIntervalEmbedding depth j) S j hfine
    (insertedInitialBody m oldBody upperBody lowerBody) oldBody
    (tau_after_eq href hmj) (theta_after_eq href hmj)
    (insertedInitialBody_after m j hmj oldBody upperBody lowerBody)

theorem canonicalTerminalConcentration_before_eq
    {depth : Nat} (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (m j : Fin depth) (rho : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1))
    (href : ScaleSequenceRefinesAt S m rho S') (hjm : j < m)
    (hfine : fine.refinement.refined.Nonempty)
    (oldBody : Fin depth -> ConvexBody Space)
    (upperBody lowerBody : ConvexBody Space) :
    let F' := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S' hfine
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S hfine
    concentration
        (effectiveActiveFamily
          (F'.hierarchy (beforeIntervalEmbedding depth j)) 1)
        (canonicalTestBody
          (F'.hierarchy (beforeIntervalEmbedding depth j))
          (insertedInitialBody m oldBody upperBody lowerBody
            (beforeIntervalEmbedding depth j)) 1) =
      concentration (effectiveActiveFamily (F.hierarchy j) 1)
        (canonicalTestBody (F.hierarchy j) (oldBody j) 1) := by
  exact canonicalTerminalConcentration_eq_of_endpoints C S'
    (beforeIntervalEmbedding depth j) S j hfine
    (insertedInitialBody m oldBody upperBody lowerBody) oldBody
    (tau_before_eq href hjm) (theta_before_eq href hjm)
    (insertedInitialBody_before m j hjm oldBody upperBody lowerBody)

theorem canonicalTerminalConcentration_after_eq
    {depth : Nat} (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (m j : Fin depth) (rho : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1))
    (href : ScaleSequenceRefinesAt S m rho S') (hmj : m < j)
    (hfine : fine.refinement.refined.Nonempty)
    (oldBody : Fin depth -> ConvexBody Space)
    (upperBody lowerBody : ConvexBody Space) :
    let F' := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S' hfine
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S hfine
    concentration
        (effectiveActiveFamily
          (F'.hierarchy (afterIntervalEmbedding depth j)) 1)
        (canonicalTestBody
          (F'.hierarchy (afterIntervalEmbedding depth j))
          (insertedInitialBody m oldBody upperBody lowerBody
            (afterIntervalEmbedding depth j)) 1) =
      concentration (effectiveActiveFamily (F.hierarchy j) 1)
        (canonicalTestBody (F.hierarchy j) (oldBody j) 1) := by
  exact canonicalTerminalConcentration_eq_of_endpoints C S'
    (afterIntervalEmbedding depth j) S j hfine
    (insertedInitialBody m oldBody upperBody lowerBody) oldBody
    (tau_after_eq href hmj) (theta_after_eq href hmj)
    (insertedInitialBody_after m j hmj oldBody upperBody lowerBody)

/-- Terminal normalization for an inserted canonical family is automatic on
all untouched intervals.  Its only fresh inputs are the two child terminal
bounds. -/
theorem canonicalInsertedTerminal_top_le_one
    {depth : Nat} (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1))
    (href : ScaleSequenceRefinesAt S m rho S')
    (hfine : fine.refinement.refined.Nonempty)
    (oldBody : Fin depth -> ConvexBody Space)
    (upperBody lowerBody : ConvexBody Space)
    (oldTerminal : forall j,
      let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S hfine
      concentration (effectiveActiveFamily (F.hierarchy j) 1)
          (canonicalTestBody (F.hierarchy j) (oldBody j) 1) <= 1)
    (upperTerminal :
      let F' := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S' hfine
      concentration
          (effectiveActiveFamily (F'.hierarchy (upperChildIndex m)) 1)
          (canonicalTestBody (F'.hierarchy (upperChildIndex m)) upperBody 1) <=
        1)
    (lowerTerminal :
      let F' := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S' hfine
      concentration
          (effectiveActiveFamily (F'.hierarchy (lowerChildIndex m)) 1)
          (canonicalTestBody (F'.hierarchy (lowerChildIndex m)) lowerBody 1) <=
        1) :
    forall k,
      let F' := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S' hfine
      concentration (effectiveActiveFamily (F'.hierarchy k) 1)
          (canonicalTestBody (F'.hierarchy k)
            (insertedInitialBody m oldBody upperBody lowerBody k) 1) <= 1 := by
  intro k
  dsimp only
  refine Fin.succAboveCases
    (α := fun k : Fin (depth + 1) =>
      let F' := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S' hfine
      concentration (effectiveActiveFamily (F'.hierarchy k) 1)
          (canonicalTestBody (F'.hierarchy k)
            (insertedInitialBody m oldBody upperBody lowerBody k) 1) <= 1)
    (lowerChildIndex m)
    (by simpa only [insertedInitialBody_lowerChild] using lowerTerminal) ?_ k
  intro j
  rcases lt_trichotomy j m with hjm | hjm | hmj
  · rw [lowerChild_succAbove_eq_before m j hjm]
    calc
      concentration
          (effectiveActiveFamily
            ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C S' hfine).hierarchy
              (beforeIntervalEmbedding depth j)) 1)
          (canonicalTestBody
            ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C S' hfine).hierarchy
              (beforeIntervalEmbedding depth j))
            (insertedInitialBody m oldBody upperBody lowerBody
              (beforeIntervalEmbedding depth j)) 1) =
        concentration
          (effectiveActiveFamily
            ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C S hfine).hierarchy j) 1)
          (canonicalTestBody
            ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C S hfine).hierarchy j)
            (oldBody j) 1) :=
        canonicalTerminalConcentration_before_eq C S m j rho S' href hjm
          hfine oldBody upperBody lowerBody
      _ <= 1 := oldTerminal j
  · subst j
    rw [lowerChild_succAbove_eq_upper]
    simpa only [insertedInitialBody_upperChild] using upperTerminal
  · rw [lowerChild_succAbove_eq_after m j hmj]
    calc
      concentration
          (effectiveActiveFamily
            ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C S' hfine).hierarchy
              (afterIntervalEmbedding depth j)) 1)
          (canonicalTestBody
            ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C S' hfine).hierarchy
              (afterIntervalEmbedding depth j))
            (insertedInitialBody m oldBody upperBody lowerBody
              (afterIntervalEmbedding depth j)) 1) =
        concentration
          (effectiveActiveFamily
            ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C S hfine).hierarchy j) 1)
          (canonicalTestBody
            ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C S hfine).hierarchy j)
            (oldBody j) 1) :=
        canonicalTerminalConcentration_after_eq C S m j rho S' href hmj
          hfine oldBody upperBody lowerBody
      _ <= 1 := oldTerminal j

/-! ## Canonical depth-one stopping states -/

/-- An honest realization of a recursive stopping state by the canonical
depth-one coherent hierarchy.  This is precisely the structural datum absent
from the generic `HierarchyStoppingState`; no equality to an arbitrary
buffered family is postulated. -/
structure CanonicalOneStepStoppingData
    (C : CoherentStickyMultiscaleCover fine)
    (N : Nat) (gapEpsilon : Real) (eta : Nat -> Real) where
  depth : Nat
  depth_pos : 0 < depth
  fine_refined_nonempty : fine.refinement.refined.Nonempty
  scales : FiniteScaleSequence delta depth
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  initialBody : Fin depth -> ConvexBody Space
  initialVolume_pos : forall m,
    0 < volume (initialBody m : Set Space)
  terminal_top_le_one : forall m,
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence C scales
      fine_refined_nonempty
    concentration (effectiveActiveFamily (F.hierarchy m) 1)
        (canonicalTestBody (F.hierarchy m) (initialBody m) 1) <= 1
  canonicalEnvelope_upper : forall m,
    canonicalHierarchyEnvelopeAt
        (CoherentExactHierarchyFamily.ofFiniteScaleSequence C scales
          fine_refined_nonempty)
        (by omega) initialBody m <=
      requiredGlobalPowerAt scales eta stage m

namespace CanonicalOneStepStoppingData

variable (C : CoherentStickyMultiscaleCover fine)
  (Q : CanonicalOneStepStoppingData C N gapEpsilon eta)

/-- The canonical buffered hierarchy already determined by the stopping
datum. -/
def buffered (delta_pos : 0 < delta) : BufferedChainFamily Q.depth 1 :=
  canonicalOneStepBufferedChainFamily C Q.scales Q.fine_refined_nonempty
    delta_pos Q.initialBody Q.initialVolume_pos Q.terminal_top_le_one

@[simp] theorem buffered_hierarchy (delta_pos : 0 < delta)
    (m : Fin Q.depth) :
    (Q.buffered C delta_pos).hierarchy m =
      (CoherentExactHierarchyFamily.ofFiniteScaleSequence C Q.scales
        Q.fine_refined_nonempty).hierarchy m := by
  rfl

/-- Forget the canonical realization to the abstract recursive state.  Its
global envelope field follows from the exact envelope expansion, rather than
being separately assumed. -/
def toState (delta_pos : 0 < delta) :
    HierarchyStoppingState delta N gapEpsilon eta where
  depth := Q.depth
  depth_pos := Q.depth_pos
  chainDepth := 1
  scales := Q.scales
  buffered := Q.buffered C delta_pos
  stage := Q.stage
  stage_pos := Q.stage_pos
  stage_le := Q.stage_le
  globalEnvelope_upper := by
    intro m
    change hierarchyGlobalEnvelopeAt
        (canonicalBufferedChainFamily
          (CoherentExactHierarchyFamily.ofFiniteScaleSequence C Q.scales
            Q.fine_refined_nonempty)
          (by omega) delta_pos Q.initialBody Q.initialVolume_pos
          Q.terminal_top_le_one) m <=
      requiredGlobalPowerAt Q.scales eta Q.stage m
    rw [hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_eq]
    exact Q.canonicalEnvelope_upper m

@[simp] theorem toState_depth (delta_pos : 0 < delta) :
    (Q.toState C delta_pos).depth = Q.depth := rfl

@[simp] theorem toState_chainDepth (delta_pos : 0 < delta) :
    (Q.toState C delta_pos).chainDepth = 1 := rfl

@[simp] theorem toState_scales (delta_pos : 0 < delta) :
    (Q.toState C delta_pos).scales = Q.scales := rfl

@[simp] theorem toState_buffered (delta_pos : 0 < delta) :
    (Q.toState C delta_pos).buffered = Q.buffered C delta_pos := rfl

@[simp] theorem toState_stage (delta_pos : 0 < delta) :
    (Q.toState C delta_pos).stage = Q.stage := rfl

end CanonicalOneStepStoppingData

/-! ## Canonical family after the selected insertion -/

variable
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (Q : CanonicalOneStepStoppingData C N gapEpsilon eta)
    (bad : SelectedActualBadSplit C (Q.toState C delta_pos))

/-- The exact coherent family on all intervals after the literal insertion. -/
def insertedExactFamily :
    CoherentExactHierarchyFamily C (Q.depth + 1) 1 :=
  CoherentExactHierarchyFamily.ofFiniteScaleSequence C
    (bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos)
    Q.fine_refined_nonempty

/-- New initial bodies: supplied bodies on the two children and literal old
bodies on every untouched interval. -/
def insertedBody (upperBody lowerBody : ConvexBody Space) :
    Fin (Q.depth + 1) -> ConvexBody Space :=
  insertedInitialBody bad.selectedStep Q.initialBody upperBody lowerBody

@[simp] theorem insertedBody_upperChild
    (upperBody lowerBody : ConvexBody Space) :
    insertedBody C delta_pos Q bad upperBody lowerBody
        (upperChildIndex bad.selectedStep) = upperBody := by
  exact insertedInitialBody_upperChild bad.selectedStep Q.initialBody
    upperBody lowerBody

@[simp] theorem insertedBody_lowerChild
    (upperBody lowerBody : ConvexBody Space) :
    insertedBody C delta_pos Q bad upperBody lowerBody
        (lowerChildIndex bad.selectedStep) = lowerBody := by
  exact insertedInitialBody_lowerChild bad.selectedStep Q.initialBody
    upperBody lowerBody

theorem insertedBody_before (upperBody lowerBody : ConvexBody Space)
    (j : Fin Q.depth) (hjm : j < bad.selectedStep) :
    insertedBody C delta_pos Q bad upperBody lowerBody
        (beforeIntervalEmbedding Q.depth j) = Q.initialBody j := by
  exact insertedInitialBody_before bad.selectedStep j hjm Q.initialBody
    upperBody lowerBody

theorem insertedBody_after (upperBody lowerBody : ConvexBody Space)
    (j : Fin Q.depth) (hmj : bad.selectedStep < j) :
    insertedBody C delta_pos Q bad upperBody lowerBody
        (afterIntervalEmbedding Q.depth j) = Q.initialBody j := by
  exact insertedInitialBody_after bad.selectedStep j hmj Q.initialBody
    upperBody lowerBody

/-- Positivity of the inserted body family needs new input only on the two
children. -/
theorem insertedBody_volume_pos
    (upperBody lowerBody : ConvexBody Space)
    (upperVolume_pos : 0 < volume (upperBody : Set Space))
    (lowerVolume_pos : 0 < volume (lowerBody : Set Space)) :
    forall k, 0 < volume
      (insertedBody C delta_pos Q bad upperBody lowerBody k :
        Set Space) := by
  exact insertedInitialBody_volume_pos bad.selectedStep Q.initialBody
    upperBody lowerBody Q.initialVolume_pos upperVolume_pos lowerVolume_pos

/-- The old terminal bounds transport to every untouched interval; the two
displayed child bounds are the only new terminal inputs. -/
theorem insertedTerminal_top_le_one
    (upperBody lowerBody : ConvexBody Space)
    (upperTerminal :
      concentration
          (effectiveActiveFamily
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (upperChildIndex bad.selectedStep)) 1)
          (canonicalTestBody
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (upperChildIndex bad.selectedStep)) upperBody 1) <= 1)
    (lowerTerminal :
      concentration
          (effectiveActiveFamily
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (lowerChildIndex bad.selectedStep)) 1)
          (canonicalTestBody
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (lowerChildIndex bad.selectedStep)) lowerBody 1) <= 1) :
    forall k,
      concentration
          (effectiveActiveFamily
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy k) 1)
          (canonicalTestBody
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy k)
            (insertedBody C delta_pos Q bad upperBody lowerBody k) 1) <= 1 := by
  let S' := bad.refinedScales C (Q.toState C delta_pos)
    gap_nonneg delta_pos
  let href := bad.refinedScales_refinesAt C (Q.toState C delta_pos)
    gap_nonneg delta_pos
  change forall k,
    let F' := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S'
      Q.fine_refined_nonempty
    concentration (effectiveActiveFamily (F'.hierarchy k) 1)
        (canonicalTestBody (F'.hierarchy k)
          (insertedInitialBody bad.selectedStep Q.initialBody
            upperBody lowerBody k) 1) <= 1
  exact canonicalInsertedTerminal_top_le_one C Q.scales bad.selectedStep
    bad.rho S' href Q.fine_refined_nonempty Q.initialBody upperBody lowerBody
    Q.terminal_top_le_one upperTerminal lowerTerminal

/-- The complete canonical buffered family after insertion. -/
def insertedBufferedFamily
    (upperBody lowerBody : ConvexBody Space)
    (upperVolume_pos : 0 < volume (upperBody : Set Space))
    (lowerVolume_pos : 0 < volume (lowerBody : Set Space))
    (upperTerminal :
      concentration
          (effectiveActiveFamily
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (upperChildIndex bad.selectedStep)) 1)
          (canonicalTestBody
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (upperChildIndex bad.selectedStep)) upperBody 1) <= 1)
    (lowerTerminal :
      concentration
          (effectiveActiveFamily
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (lowerChildIndex bad.selectedStep)) 1)
          (canonicalTestBody
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (lowerChildIndex bad.selectedStep)) lowerBody 1) <= 1) :
    BufferedChainFamily (Q.depth + 1) 1 :=
  canonicalBufferedChainFamily
    (insertedExactFamily C gap_nonneg delta_pos Q bad) (by omega) delta_pos
    (insertedBody C delta_pos Q bad upperBody lowerBody)
    (insertedBody_volume_pos C delta_pos Q bad upperBody lowerBody
      upperVolume_pos lowerVolume_pos)
    (insertedTerminal_top_le_one C gap_nonneg delta_pos Q bad upperBody
      lowerBody upperTerminal lowerTerminal)


/-! ## Untouched hierarchy envelopes are equal, not assumed -/

theorem insertedBufferedFamily_beforeEnvelope_eq
    (upperBody lowerBody : ConvexBody Space)
    (upperVolume_pos : 0 < volume (upperBody : Set Space))
    (lowerVolume_pos : 0 < volume (lowerBody : Set Space))
    (upperTerminal :
      concentration
          (effectiveActiveFamily
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (upperChildIndex bad.selectedStep)) 1)
          (canonicalTestBody
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (upperChildIndex bad.selectedStep)) upperBody 1) <= 1)
    (lowerTerminal :
      concentration
          (effectiveActiveFamily
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (lowerChildIndex bad.selectedStep)) 1)
          (canonicalTestBody
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (lowerChildIndex bad.selectedStep)) lowerBody 1) <= 1)
    (j : Fin Q.depth) (hjm : j < bad.selectedStep) :
    hierarchyGlobalEnvelopeAt
        (insertedBufferedFamily C gap_nonneg delta_pos Q bad upperBody
          lowerBody upperVolume_pos lowerVolume_pos upperTerminal lowerTerminal)
        (beforeIntervalEmbedding Q.depth j) =
      hierarchyGlobalEnvelopeAt (Q.toState C delta_pos).buffered j := by
  let S' := bad.refinedScales C (Q.toState C delta_pos)
    gap_nonneg delta_pos
  let href := bad.refinedScales_refinesAt C (Q.toState C delta_pos)
    gap_nonneg delta_pos
  change hierarchyGlobalEnvelopeAt
      (canonicalBufferedChainFamily
        (insertedExactFamily C gap_nonneg delta_pos Q bad) (by omega)
        delta_pos (insertedBody C delta_pos Q bad upperBody lowerBody)
        (insertedBody_volume_pos C delta_pos Q bad upperBody lowerBody
          upperVolume_pos lowerVolume_pos)
        (insertedTerminal_top_le_one C gap_nonneg delta_pos Q bad upperBody
          lowerBody upperTerminal lowerTerminal))
      (beforeIntervalEmbedding Q.depth j) =
    hierarchyGlobalEnvelopeAt
      (canonicalBufferedChainFamily
        (CoherentExactHierarchyFamily.ofFiniteScaleSequence C Q.scales
          Q.fine_refined_nonempty)
        (by omega) delta_pos Q.initialBody Q.initialVolume_pos
        Q.terminal_top_le_one) j
  rw [hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_eq,
    hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_eq]
  exact canonicalHierarchyEnvelopeAt_before_eq C Q.scales bad.selectedStep j
    bad.rho S' href hjm Q.fine_refined_nonempty Q.initialBody upperBody
    lowerBody

theorem insertedBufferedFamily_afterEnvelope_eq
    (upperBody lowerBody : ConvexBody Space)
    (upperVolume_pos : 0 < volume (upperBody : Set Space))
    (lowerVolume_pos : 0 < volume (lowerBody : Set Space))
    (upperTerminal :
      concentration
          (effectiveActiveFamily
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (upperChildIndex bad.selectedStep)) 1)
          (canonicalTestBody
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (upperChildIndex bad.selectedStep)) upperBody 1) <= 1)
    (lowerTerminal :
      concentration
          (effectiveActiveFamily
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (lowerChildIndex bad.selectedStep)) 1)
          (canonicalTestBody
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (lowerChildIndex bad.selectedStep)) lowerBody 1) <= 1)
    (j : Fin Q.depth) (hmj : bad.selectedStep < j) :
    hierarchyGlobalEnvelopeAt
        (insertedBufferedFamily C gap_nonneg delta_pos Q bad upperBody
          lowerBody upperVolume_pos lowerVolume_pos upperTerminal lowerTerminal)
        (afterIntervalEmbedding Q.depth j) =
      hierarchyGlobalEnvelopeAt (Q.toState C delta_pos).buffered j := by
  let S' := bad.refinedScales C (Q.toState C delta_pos)
    gap_nonneg delta_pos
  let href := bad.refinedScales_refinesAt C (Q.toState C delta_pos)
    gap_nonneg delta_pos
  change hierarchyGlobalEnvelopeAt
      (canonicalBufferedChainFamily
        (insertedExactFamily C gap_nonneg delta_pos Q bad) (by omega)
        delta_pos (insertedBody C delta_pos Q bad upperBody lowerBody)
        (insertedBody_volume_pos C delta_pos Q bad upperBody lowerBody
          upperVolume_pos lowerVolume_pos)
        (insertedTerminal_top_le_one C gap_nonneg delta_pos Q bad upperBody
          lowerBody upperTerminal lowerTerminal))
      (afterIntervalEmbedding Q.depth j) =
    hierarchyGlobalEnvelopeAt
      (canonicalBufferedChainFamily
        (CoherentExactHierarchyFamily.ofFiniteScaleSequence C Q.scales
          Q.fine_refined_nonempty)
        (by omega) delta_pos Q.initialBody Q.initialVolume_pos
        Q.terminal_top_le_one) j
  rw [hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_eq,
    hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_eq]
  exact canonicalHierarchyEnvelopeAt_after_eq C Q.scales bad.selectedStep j
    bad.rho S' href hmj Q.fine_refined_nonempty Q.initialBody upperBody
    lowerBody

/-! ## Final local-certificate assembler -/

/-- A canonical insertion closes both untouched-envelope fields
automatically.  Beyond the two supplied child bodies and their positive
volumes, the only new analytic inputs are the two child terminal bounds and
the two child target-envelope bounds displayed below. -/
def localEnvelopeRefinementCertificate_of_canonicalInsertion
    (upperBody lowerBody : ConvexBody Space)
    (upperVolume_pos : 0 < volume (upperBody : Set Space))
    (lowerVolume_pos : 0 < volume (lowerBody : Set Space))
    (upperTerminal :
      concentration
          (effectiveActiveFamily
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (upperChildIndex bad.selectedStep)) 1)
          (canonicalTestBody
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (upperChildIndex bad.selectedStep)) upperBody 1) <= 1)
    (lowerTerminal :
      concentration
          (effectiveActiveFamily
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (lowerChildIndex bad.selectedStep)) 1)
          (canonicalTestBody
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
              (lowerChildIndex bad.selectedStep)) lowerBody 1) <= 1)
    (upperEnvelope_upper :
      hierarchyGlobalEnvelopeAt
          (insertedBufferedFamily C gap_nonneg delta_pos Q bad upperBody
            lowerBody upperVolume_pos lowerVolume_pos upperTerminal
            lowerTerminal)
          (upperChildIndex bad.selectedStep) <=
        requiredGlobalPowerAt
          (bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos)
          eta (Q.stage + 1) (upperChildIndex bad.selectedStep))
    (lowerEnvelope_upper :
      hierarchyGlobalEnvelopeAt
          (insertedBufferedFamily C gap_nonneg delta_pos Q bad upperBody
            lowerBody upperVolume_pos lowerVolume_pos upperTerminal
            lowerTerminal)
          (lowerChildIndex bad.selectedStep) <=
        requiredGlobalPowerAt
          (bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos)
          eta (Q.stage + 1) (lowerChildIndex bad.selectedStep)) :
    LocalEnvelopeRefinementCertificate C gap_nonneg delta_pos
      (Q.toState C delta_pos) bad where
  newChainDepth := 1
  newBuffered := insertedBufferedFamily C gap_nonneg delta_pos Q bad
    upperBody lowerBody upperVolume_pos lowerVolume_pos upperTerminal
    lowerTerminal
  beforeEnvelope_le := by
    intro j hjm
    exact (insertedBufferedFamily_beforeEnvelope_eq C gap_nonneg delta_pos Q
      bad upperBody lowerBody upperVolume_pos lowerVolume_pos upperTerminal
      lowerTerminal j hjm).le
  afterEnvelope_le := by
    intro j hmj
    exact (insertedBufferedFamily_afterEnvelope_eq C gap_nonneg delta_pos Q
      bad upperBody lowerBody upperVolume_pos lowerVolume_pos upperTerminal
      lowerTerminal j hmj).le
  upperChildEnvelope_upper := upperEnvelope_upper
  lowerChildEnvelope_upper := lowerEnvelope_upper

#print axioms insertedInitialBody_volume_pos
#print axioms ofAdjacentInterval_eq_of_endpoints
#print axioms canonicalHierarchyEnvelopeAt_eq_of_endpoints
#print axioms canonicalInsertedTerminal_top_le_one
#print axioms CanonicalOneStepStoppingData.toState
#print axioms insertedBufferedFamily_beforeEnvelope_eq
#print axioms insertedBufferedFamily_afterEnvelope_eq
#print axioms localEnvelopeRefinementCertificate_of_canonicalInsertion

end
end FamilyStickyScaleChainCanonicalInsertionEnvelopeTransportV2
