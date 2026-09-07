import Family8Grounding.Family8GeneralizedKatzTaoMultiplicityV1

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8RestrictedActualDatumMassBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Exact convex mass transport to a restricted actual datum

The zero-colour sample is represented by a genuine subtype-indexed datum.
This file identifies its ordinary `containedMass` with the source family's
`containedMassOn` over the selected indices.  Consequently Katz--Tao control
proved for source-indexed sampled weights applies literally to the datum to
which `KatzTaoProperty` is later applied.
-/

/-- A source tube body and the corresponding body in the selected subtype are
definitionally the same convex body. -/
@[simp] theorem restrictActualTubeDatum_bodyFamily_apply
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (selected : Finset iota)
    (i : {i // i ∈ selected}) :
    (restrictActualTubeDatum D selected).family.bodyFamily i =
      D.family.bodyFamily i.1 := by
  rfl

/-- Containment in a convex test body is preserved exactly by restriction to
the selected subtype. -/
@[simp] theorem restrictActualTubeDatum_mem_containedIndices
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (selected : Finset iota)
    (K : ConvexBody Space) (i : {i // i ∈ selected}) :
    i ∈ containedIndices
        (restrictActualTubeDatum D selected).family.bodyFamily K ↔
      i.1 ∈ containedIndices D.family.bodyFamily K := by
  rw [mem_containedIndices, mem_containedIndices]
  rfl

/-- Ordinary contained mass of the genuine subtype datum is exactly the
active contained mass of the source family. -/
theorem restrictActualTubeDatum_containedMass
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (selected : Finset iota)
    (K : ConvexBody Space) :
    containedMass (restrictActualTubeDatum D selected).family.bodyFamily K =
      containedMassOn D.family.bodyFamily selected K := by
  classical
  simp [containedMass, containedMassOn, containedIndices,
    restrictActualTubeDatum_bodyFamily_apply]
  rw [Finset.filter_attach']
  simp
  refine (Finset.sum_attach
    ({x ∈ selected | ∃ h : x ∈ selected,
      D.family.bodyFamily (⟨x, h⟩ : {x // x ∈ selected}) ≤ K})
    (fun i => volume (D.family.bodyFamily i : Set Space))).trans ?_
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

/-- The exact bridge specialized to the actual zero-colour sampled datum. -/
theorem zeroColorActualDatum_containedMass
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (k : Nat) [NeZero k]
    (omega : iota → Fin k) (K : ConvexBody Space) :
    containedMass (zeroColorActualDatum D k omega).family.bodyFamily K =
      containedMassOn D.family.bodyFamily (zeroColorSample k omega) K := by
  exact restrictActualTubeDatum_containedMass D (zeroColorSample k omega) K

#print axioms restrictActualTubeDatum_bodyFamily_apply
#print axioms restrictActualTubeDatum_mem_containedIndices
#print axioms restrictActualTubeDatum_containedMass
#print axioms zeroColorActualDatum_containedMass

end
end Family8RestrictedActualDatumMassBridgeV1
