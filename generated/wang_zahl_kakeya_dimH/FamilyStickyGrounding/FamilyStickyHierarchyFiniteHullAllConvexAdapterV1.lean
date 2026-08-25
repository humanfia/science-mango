import FamilyStickyGrounding.FamilyStickyHierarchyRandomMotionCertificateV1
import FamilyStickyGrounding.JohnCapturedTubeCertificateCleanAdapterV1
import Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace FamilyStickyHierarchyFiniteHullAllConvexAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open FamilyStickyActualTubeTranslationV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyRandomMotionCertificateV1
open FamilyStickyHierarchyRandomMotionCertificateV1.HierarchySharedMotionCertificate
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1.DependentMultiscaleAllParentSourceData

noncomputable section

/-!
# Finite hull tests imply all-convex control

For a finite convex family, the mass captured by a test body depends only on
the subset of family members contained in it.  If that subset is nonempty,
the closed convex hull of its union is contained in the original test body
and captures exactly the same members.  Consequently the finitely many
nonempty subsets give an exact test catalogue; no compactness or net on the
space of convex bodies is needed.

The second half applies this observation to the literal occurrence family
created at one parent and one level of a hierarchy shared-motion
certificate.  Every canonical hull contains a positive-radius translated
tube, so the existing John theorem equips it automatically with a
`BoxDimensionsCertificate 288`.  The construction is deliberately
post-motion: using these tests inside the random selector itself would still
require a pre-selection catalogue of every possible motion outcome.
-/

namespace CanonicalHullTests

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite type of nonempty subsets of the whole occurrence index. -/
abbrev Index (_F : ConvexFamily ι) :=
  {s : Finset ι // s ∈ hullCandidates (Finset.univ : Finset ι)}

/-- A fixed enumeration by `Fin`, matching the random-motion test API. -/
noncomputable def indexEquivFin (F : ConvexFamily ι) :
    Index F ≃ Fin (Fintype.card (Index F)) :=
  Fintype.equivFin _

/-- The nonempty subset represented by a finite test index. -/
noncomputable def subsetAt (F : ConvexFamily ι)
    (q : Fin (Fintype.card (Index F))) : Finset ι :=
  ((indexEquivFin F).symm q).1

theorem subsetAt_mem (F : ConvexFamily ι)
    (q : Fin (Fintype.card (Index F))) :
    subsetAt F q ∈ hullCandidates (Finset.univ : Finset ι) :=
  ((indexEquivFin F).symm q).2

theorem subsetAt_nonempty (F : ConvexFamily ι)
    (q : Fin (Fintype.card (Index F))) :
    (subsetAt F q).Nonempty :=
  (mem_hullCandidates.mp (subsetAt_mem F q)).2

/-- The canonical test body attached to a nonempty subset. -/
noncomputable def body (F : ConvexFamily ι)
    (q : Fin (Fintype.card (Index F))) : ConvexBody Space :=
  hullContainer F (subsetAt F q)

/-- Every nonempty subset occurs exactly in the finite enumeration. -/
theorem subsetAt_indexEquivFin
    (F : ConvexFamily ι) (s : Finset ι)
    (hs : s ∈ hullCandidates (Finset.univ : Finset ι)) :
    subsetAt F (indexEquivFin F ⟨s, hs⟩) = s := by
  simp [subsetAt]

/-- The catalogue has at most one test for every subset of the index type. -/
theorem card_index_le_two_pow (F : ConvexFamily ι) :
    Fintype.card (Index F) ≤ 2 ^ Fintype.card ι := by
  calc
    Fintype.card (Index F) ≤ Fintype.card (Finset ι) :=
      Fintype.card_le_of_injective
        (fun s : Index F => s.1)
        (fun _ _ h => Subtype.ext h)
    _ = 2 ^ Fintype.card ι := Fintype.card_finset

/-- Exact finite-support reduction for cross-multiplied Katz--Tao bounds.
Only the explicitly enumerated hull bodies have to be checked. -/
theorem isKatzTao_of_finite_hull_tests
    (F : ConvexFamily ι) (A : ENNReal)
    (hfinite : ∀ q, IsKatzTaoAt A F (body F q)) :
    IsKatzTao A F := by
  classical
  intro K
  let s : Finset ι := containedIndices F K
  by_cases hs : s.Nonempty
  · have hsCandidate : s ∈ hullCandidates (Finset.univ : Finset ι) := by
      exact mem_hullCandidates.mpr ⟨Finset.subset_univ s, hs⟩
    let q : Fin (Fintype.card (Index F)) := indexEquivFin F ⟨s, hsCandidate⟩
    have hq : subsetAt F q = s := by
      exact subsetAt_indexEquivFin F s hsCandidate
    have hbody : (body F q : Set Space) ⊆ (K : Set Space) := by
      rw [body, hq]
      apply hullContainer_subset F hs
      intro i hi
      exact (mem_containedIndices F K i).mp hi
    have hindices : containedIndices F (body F q) = containedIndices F K := by
      ext i
      rw [mem_containedIndices, mem_containedIndices]
      constructor
      · intro hi
        exact hi.trans hbody
      · intro hi
        rw [body, hq]
        exact body_subset_hullContainer F
          ((show i ∈ s from (mem_containedIndices F K i).mpr hi)) hs
    have hmass : containedMass F (body F q) = containedMass F K := by
      unfold containedMass
      rw [hindices]
    calc
      containedMass F K = containedMass F (body F q) := hmass.symm
      _ ≤ A * volume (body F q : Set Space) := hfinite q
      _ ≤ A * volume (K : Set Space) := by
        gcongr
  · have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    unfold IsKatzTaoAt containedMass
    rw [show containedIndices F K = ∅ from hsEmpty]
    simp

end CanonicalHullTests

namespace TubeCanonicalHullTests

variable {δ : NNReal} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Convex family underlying a finite indexed tube family. -/
def tubeFamily (T : ι → Tube δ) : ConvexFamily ι :=
  fun i => (T i).body

/-- One member of the nonempty subset represented by a canonical test. -/
noncomputable def witnessIndex (T : ι → Tube δ)
    (q : Fin (Fintype.card (CanonicalHullTests.Index (tubeFamily T)))) : ι :=
  Classical.choose (CanonicalHullTests.subsetAt_nonempty (tubeFamily T) q)

theorem witnessIndex_mem (T : ι → Tube δ)
    (q : Fin (Fintype.card (CanonicalHullTests.Index (tubeFamily T)))) :
    witnessIndex T q ∈ CanonicalHullTests.subsetAt (tubeFamily T) q :=
  Classical.choose_spec (CanonicalHullTests.subsetAt_nonempty (tubeFamily T) q)

/-- The witness tube is contained in its canonical closed hull. -/
theorem witnessTube_subset_body (T : ι → Tube δ)
    (q : Fin (Fintype.card (CanonicalHullTests.Index (tubeFamily T)))) :
    (T (witnessIndex T q)).carrier ⊆
      (CanonicalHullTests.body (tubeFamily T) q : Set Space) := by
  change (tubeFamily T (witnessIndex T q) : Set Space) ⊆ _
  exact body_subset_hullContainer (tubeFamily T) (witnessIndex_mem T q)
    (CanonicalHullTests.subsetAt_nonempty (tubeFamily T) q)

/-- Positive John data for one canonical hull test. -/
structure PositiveJohnData (T : ι → Tube δ)
    (q : Fin (Fintype.card (CanonicalHullTests.Index (tubeFamily T)))) where
  side : Fin 3 → NNReal
  side_pos : ∀ i, 0 < side i
  certificate : BoxDimensionsCertificate 288 side
    (CanonicalHullTests.body (tubeFamily T) q)

/-- Every canonical hull admits positive `288`-John data because it contains
its selected positive-radius tube. -/
theorem positiveJohnData_nonempty (hδ : 0 < δ) (T : ι → Tube δ)
    (q : Fin (Fintype.card (CanonicalHullTests.Index (tubeFamily T)))) :
    Nonempty (PositiveJohnData T q) := by
  obtain ⟨side, hside, ⟨cert⟩⟩ :=
    exists_positive_boxDimensionsCertificate_288_of_tube_subset_clean
      (CanonicalHullTests.body (tubeFamily T) q) (T (witnessIndex T q)) hδ
      (witnessTube_subset_body T q)
  exact ⟨⟨side, hside, cert⟩⟩

/-- A fixed positive John witness for each canonical hull. -/
noncomputable def positiveJohnData (hδ : 0 < δ) (T : ι → Tube δ)
    (q : Fin (Fintype.card (CanonicalHullTests.Index (tubeFamily T)))) :
    PositiveJohnData T q :=
  Classical.choice (positiveJohnData_nonempty hδ T q)

/-- The exact finite canonical hull catalogue, in the data format consumed
by the hierarchy random-motion layer. -/
noncomputable def boxCertifiedTestFamily (hδ : 0 < δ) (T : ι → Tube δ) :
    BoxCertifiedTestFamily where
  testCard := Fintype.card (CanonicalHullTests.Index (tubeFamily T))
  testBody := CanonicalHullTests.body (tubeFamily T)
  activeTests := Finset.univ
  Cbox := 288
  side := fun q => (positiveJohnData hδ T q).side
  certificate := fun q => (positiveJohnData hδ T q).certificate

@[simp] theorem boxCertifiedTestFamily_activeTests
    (hδ : 0 < δ) (T : ι → Tube δ) :
    (boxCertifiedTestFamily hδ T).activeTests = Finset.univ := rfl

@[simp] theorem boxCertifiedTestFamily_testBody
    (hδ : 0 < δ) (T : ι → Tube δ)
    (q : Fin (boxCertifiedTestFamily hδ T).testCard) :
    (boxCertifiedTestFamily hδ T).testBody q =
      CanonicalHullTests.body (tubeFamily T) q := rfl

theorem boxCertifiedTestFamily_side_pos
    (hδ : 0 < δ) (T : ι → Tube δ)
    (q : Fin (boxCertifiedTestFamily hδ T).testCard) (i : Fin 3) :
    0 < (boxCertifiedTestFamily hδ T).side q i :=
  (positiveJohnData hδ T q).side_pos i

/-- Checking the finite John-certified catalogue proves the full
all-convex-body Katz--Tao assertion for the tube family. -/
theorem isKatzTao_of_boxCertifiedTestFamily
    (hδ : 0 < δ) (T : ι → Tube δ) (A : ENNReal)
    (hfinite : ∀ q,
      IsKatzTaoAt A (tubeFamily T)
        ((boxCertifiedTestFamily hδ T).testBody q)) :
    IsKatzTao A (tubeFamily T) := by
  apply CanonicalHullTests.isKatzTao_of_finite_hull_tests
  intro q
  simpa only [boxCertifiedTestFamily] using hfinite q

end TubeCanonicalHullTests

namespace HierarchySharedMotionCertificate

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (G : HierarchyRandomMotionGeometry H)
  (C : HierarchySharedMotionCertificate H G)

/-- Occurrences at one parent and layer: one copy for every selected motion
and every literal member of the parent fibre. -/
abbrev PrefixFiberOccurrenceIndex (k : Fin depth) (p : Index (k.1 + 1)) :=
  Fin (G.toDependentSource.repetitions k) ×
    {i // i ∈ (H.step k.1 k.2).combinatorics.index.fiber p}

/-- The actual twice-translated tube occurrence under a fixed common prefix. -/
def prefixFiberOccurrenceTube
    (path : C.Path) (k : Fin depth) (p : Index (k.1 + 1))
    (a : PrefixFiberOccurrenceIndex H G k p) :
    Tube (H.effectiveRadius k.1) :=
  translateTube
    (translateTube ((H.effectiveFamily k.1).tubes a.2.1)
      (C.output.omega k a.1))
    (Output.prefixVector G.toDependentSource C.output path k)

/-- Convex occurrence family whose all-body concentration is the genuine
post-motion target at this parent and scale. -/
def prefixFiberOccurrenceFamily
    (path : C.Path) (k : Fin depth) (p : Index (k.1 + 1)) :
    ConvexFamily (PrefixFiberOccurrenceIndex H G k p) :=
  TubeCanonicalHullTests.tubeFamily
    (prefixFiberOccurrenceTube H G C path k p)

/-- Finite canonical hull tests for the actual selected occurrence family,
with automatic positive John-288 certificates. -/
noncomputable def prefixFiberCanonicalTestFamily
    (path : C.Path) (k : Fin depth) (p : Index (k.1 + 1)) :
    BoxCertifiedTestFamily :=
  TubeCanonicalHullTests.boxCertifiedTestFamily (G.childRadius_pos k)
    (prefixFiberOccurrenceTube H G C path k p)

@[simp] theorem prefixFiberCanonicalTestFamily_Cbox
    (path : C.Path) (k : Fin depth) (p : Index (k.1 + 1)) :
    (prefixFiberCanonicalTestFamily H G C path k p).Cbox = 288 := rfl

@[simp] theorem prefixFiberCanonicalTestFamily_activeTests
    (path : C.Path) (k : Fin depth) (p : Index (k.1 + 1)) :
    (prefixFiberCanonicalTestFamily H G C path k p).activeTests =
      Finset.univ := rfl

/-- Exact Family7 finite-support adapter: a bound on the displayed finite
John-certified catalogue yields the same bound for every `ConvexBody` test
of the literal prefix occurrence family. -/
theorem prefixFiber_isKatzTao_of_finiteCanonicalTests
    (path : C.Path) (k : Fin depth) (p : Index (k.1 + 1))
    (A : ENNReal)
    (hfinite : ∀ q,
      IsKatzTaoAt A (prefixFiberOccurrenceFamily H G C path k p)
        ((prefixFiberCanonicalTestFamily H G C path k p).testBody q)) :
    IsKatzTao A (prefixFiberOccurrenceFamily H G C path k p) := by
  exact TubeCanonicalHullTests.isKatzTao_of_boxCertifiedTestFamily
    (G.childRadius_pos k) (prefixFiberOccurrenceTube H G C path k p) A hfinite

end HierarchySharedMotionCertificate

#print axioms CanonicalHullTests.subsetAt_indexEquivFin
#print axioms CanonicalHullTests.card_index_le_two_pow
#print axioms CanonicalHullTests.isKatzTao_of_finite_hull_tests
#print axioms TubeCanonicalHullTests.witnessTube_subset_body
#print axioms TubeCanonicalHullTests.positiveJohnData
#print axioms TubeCanonicalHullTests.boxCertifiedTestFamily
#print axioms TubeCanonicalHullTests.isKatzTao_of_boxCertifiedTestFamily
#print axioms HierarchySharedMotionCertificate.prefixFiberOccurrenceTube
#print axioms HierarchySharedMotionCertificate.prefixFiberCanonicalTestFamily
#print axioms HierarchySharedMotionCertificate.prefixFiber_isKatzTao_of_finiteCanonicalTests

end
end FamilyStickyHierarchyFiniteHullAllConvexAdapterV1
