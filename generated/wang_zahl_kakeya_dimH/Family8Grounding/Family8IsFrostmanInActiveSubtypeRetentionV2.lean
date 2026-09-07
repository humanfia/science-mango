import Family8Grounding.Family8Prop51SelectedOccurrenceSourceFrostmanV1
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Family8Grounding.Family8FrostmanInOnUnivBridgeV2
import Mathlib.Tactic

/-!
# Frostman transport to a retained literal subtype, V2

`IsFrostmanIn` is not monotone under restriction because its ambient
contained mass occurs in the denominator.  This file records the exact
one-scalar transport needed by the fixed-parent low-CF branch: after paying
the displayed ambient-mass retention factor, the selected literal subtype
inherits the source Frostman certificate.  V1 omitted one direct namespace
dependency and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8IsFrostmanInActiveSubtypeRetentionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1

noncomputable section

/-- Restrict a parent-normalized Frostman certificate to a literal selected
subtype, paying exactly the loss in contained mass inside the same parent.
No density, selector, or global-CF hypothesis is hidden in this transport. -/
theorem isFrostmanIn_activeSubtype_of_ambientMass_retention
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota} {K : ConvexBody Space}
    {C L : ENNReal} (selected : Finset iota)
    (hF : IsFrostmanIn C F K)
    (hretained : containedMass F K <=
      L * containedMass (activeSubtypeFamily F selected) K) :
    IsFrostmanIn (C * L) (activeSubtypeFamily F selected) K := by
  have hOn : IsFrostmanOn C F Finset.univ K := by
    refine (Family8FrostmanInOnUnivBridgeV2.isFrostmanOn_univ_iff_isFrostmanIn
      F K).2 hF
  have hretainedOn : containedMassOn F Finset.univ K <=
      L * containedMassOn F selected K := by
    simpa only [containedMassOn_univ,
      containedMass_activeSubtypeFamily] using hretained
  have hSelected : IsFrostmanOn (C * L) F selected K :=
    isFrostmanOn_subset_of_ambientMass_retention
      (Finset.subset_univ selected) hOn hretainedOn
  exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
    F selected K).1 hSelected

#print axioms isFrostmanIn_activeSubtype_of_ambientMass_retention

end
end Family8IsFrostmanInActiveSubtypeRetentionV2
