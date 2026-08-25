import FamilyStickyGrounding.FamilyStickyHierarchyFiniteHullAllConvexAdapterV1
import FamilyStickyGrounding.FamilyStickyHierarchyJointRandomMotionCertificateV1
import FamilyStickyGrounding.FamilyStickyHierarchyCollisionTestGeometryProducerV1
import FamilyStickyGrounding.FamilyStickyConvexBodyTranslationConcentrationV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace FamilyStickyHierarchyPreMotionHullTestSupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTestDataV1
open FamilyStickyActualTubeTestDataV1.ActualTubeTestData
open FamilyStickyConvexBodyTranslationConcentrationV1
open FamilyStickyHierarchyFiniteHullAllConvexAdapterV1
open FamilyStickyHierarchyFiniteHullAllConvexAdapterV1.CanonicalHullTests
open FamilyStickyHierarchyFiniteHullAllConvexAdapterV1.TubeCanonicalHullTests
open FamilyStickySharedTranslationPackingExistenceV1
open FamilyStickySharedTranslationPackingIncidenceV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyCollisionTestGeometryProducerV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1

noncomputable section

/-!
# Canonical hull tests enumerated before motion selection

The selected repetitions need not be known when the test catalogue is
built.  Fix a finite packing certificate and form the universal family of
all pairs `(packing center, active source tube)`.  Every subsequently
selected occurrence is supported on this universal family, even when the
same center is selected repeatedly.  The closed hulls of all nonempty
subsets of the universal family are therefore an exact finite catalogue for
every possible selected outcome.

The hierarchy-level plan below contains only packing certificates, not
random choices.  It constructs the catalogue before any `omega` is chosen.
The faithful joint output retains its packing index; the remaining upstream
interface issue is exact coherence between the certificate chosen by the
selector and the certificate supplied by the plan.  That equality is
isolated as `UsesPackingPlan` rather than hidden in an analytic conclusion.
-/

namespace SupportedFiniteHullTests

variable {ι σ : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- A finite hull catalogue for a universal family controls any finite
family whose members are drawn from that universal support.  The support map need not
be injective, so repeated random choices are allowed. -/
theorem isKatzTao_of_supported_finite_hull_tests
    (ambientFamily : ConvexFamily ι) (selected : ConvexFamily σ)
    (support : σ → ι)
    (hsupport : ∀ a, selected a = ambientFamily (support a))
    (A : ENNReal)
    (hfinite : ∀ q,
      IsKatzTaoAt A selected (CanonicalHullTests.body ambientFamily q)) :
    IsKatzTao A selected := by
  classical
  intro K
  let captured : Finset σ := containedIndices selected K
  let s : Finset ι := captured.image support
  by_cases hcaptured : captured.Nonempty
  · have hs : s.Nonempty := hcaptured.image support
    have hsCandidate : s ∈ hullCandidates (Finset.univ : Finset ι) :=
      mem_hullCandidates.mpr ⟨Finset.subset_univ s, hs⟩
    let q : Fin (Fintype.card (CanonicalHullTests.Index ambientFamily)) :=
      CanonicalHullTests.indexEquivFin ambientFamily ⟨s, hsCandidate⟩
    have hq : CanonicalHullTests.subsetAt ambientFamily q = s :=
      CanonicalHullTests.subsetAt_indexEquivFin ambientFamily s hsCandidate
    have hbody :
        (CanonicalHullTests.body ambientFamily q : Set Space) ⊆ (K : Set Space) := by
      rw [CanonicalHullTests.body, hq]
      apply hullContainer_subset ambientFamily hs
      intro i hi
      obtain ⟨a, ha, hai⟩ := Finset.mem_image.mp hi
      subst i
      rw [← hsupport a]
      exact (mem_containedIndices selected K a).mp ha
    have hindices :
        containedIndices selected (CanonicalHullTests.body ambientFamily q) =
          containedIndices selected K := by
      ext a
      rw [mem_containedIndices, mem_containedIndices]
      constructor
      · intro ha
        exact ha.trans hbody
      · intro ha
        have haCaptured : a ∈ captured :=
          (show a ∈ containedIndices selected K from
            (mem_containedIndices selected K a).mpr ha)
        have haSupport : support a ∈ s :=
          Finset.mem_image.mpr ⟨a, haCaptured, rfl⟩
        rw [CanonicalHullTests.body, hq, hsupport a]
        exact body_subset_hullContainer ambientFamily haSupport hs
    have hmass :
        containedMass selected (CanonicalHullTests.body ambientFamily q) =
          containedMass selected K := by
      unfold containedMass
      rw [hindices]
    calc
      containedMass selected K =
          containedMass selected (CanonicalHullTests.body ambientFamily q) :=
        hmass.symm
      _ ≤ A * volume (CanonicalHullTests.body ambientFamily q : Set Space) :=
        hfinite q
      _ ≤ A * volume (K : Set Space) := by
        gcongr
  · have hcapturedEmpty : captured = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcaptured
    unfold IsKatzTaoAt containedMass
    rw [show containedIndices selected K = ∅ from hcapturedEmpty]
    simp

end SupportedFiniteHullTests

namespace FixedPackingPotentialFamily

variable {δ motionRadius mesh : NNReal} {tubeIndex : Type*}
  [DecidableEq tubeIndex]

/-- All source-tube translates available before a random center is chosen. -/
abbrev PotentialIndex
    (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh) :=
  (↥C.centers) × {i // i ∈ D.tubes}

def potentialTube
    (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh)
    (a : PotentialIndex D C) : Tube δ :=
  translateTube (D.tube a.2.1) (a.1.1 : Space)

def potentialFamily
    (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh) :
    ConvexFamily (PotentialIndex D C) :=
  TubeCanonicalHullTests.tubeFamily (potentialTube D C)

/-- Fixed finite John-certified tests depending on the packing support but
not on the future repetition count or selected centers. -/
noncomputable def canonicalTestFamily
    (hδ : 0 < δ) (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh) :
    BoxCertifiedTestFamily :=
  TubeCanonicalHullTests.boxCertifiedTestFamily hδ (potentialTube D C)

@[simp] theorem canonicalTestFamily_Cbox
    (hδ : 0 < δ) (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh) :
    (canonicalTestFamily hδ D C).Cbox = 288 := rfl

@[simp] theorem canonicalTestFamily_activeTests
    (hδ : 0 < δ) (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh) :
    (canonicalTestFamily hδ D C).activeTests = Finset.univ := rfl

/-- Actual occurrences after choosing `J` packing centers. -/
abbrev SelectedIndex (D : ActualTubeTestData δ tubeIndex) (J : Nat) :=
  Fin J × {i // i ∈ D.tubes}

def selectedTube
    (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh)
    {J : Nat} (omega : Fin J → ↥C.centers)
    (a : SelectedIndex D J) : Tube δ :=
  translateTube (D.tube a.2.1) ((omega a.1).1 : Space)

def selectedFamily
    (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh)
    {J : Nat} (omega : Fin J → ↥C.centers) :
    ConvexFamily (SelectedIndex D J) :=
  TubeCanonicalHullTests.tubeFamily (selectedTube D C omega)

/-- Every selected occurrence remembers its position in the fixed universal
packing support. -/
def supportMap
    (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh)
    {J : Nat} (omega : Fin J → ↥C.centers) :
    SelectedIndex D J → PotentialIndex D C :=
  fun a => ⟨omega a.1, a.2⟩

@[simp] theorem selectedFamily_eq_potentialFamily_supportMap
    (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh)
    {J : Nat} (omega : Fin J → ↥C.centers)
    (a : SelectedIndex D J) :
    selectedFamily D C omega a =
      potentialFamily D C (supportMap D C omega a) := rfl

/-- The pre-motion catalogue controls every possible repeated selection from
the fixed packing, without any dependence on `J` or `omega`. -/
theorem selected_isKatzTao_of_preMotion_finite_tests
    (hδ : 0 < δ) (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh)
    {J : Nat} (omega : Fin J → ↥C.centers) (A : ENNReal)
    (hfinite : ∀ q,
      IsKatzTaoAt A (selectedFamily D C omega)
        ((canonicalTestFamily hδ D C).testBody q)) :
    IsKatzTao A (selectedFamily D C omega) := by
  apply SupportedFiniteHullTests.isKatzTao_of_supported_finite_hull_tests
    (potentialFamily D C) (selectedFamily D C omega)
    (supportMap D C omega)
    (selectedFamily_eq_potentialFamily_supportMap D C omega) A
  intro q
  simpa only [canonicalTestFamily,
    potentialFamily, TubeCanonicalHullTests.boxCertifiedTestFamily] using hfinite q

/-- A common hierarchy prefix preserves the all-convex conclusion obtained
from the fixed local catalogue. -/
theorem prefixSelected_isKatzTao_of_preMotion_finite_tests
    (hδ : 0 < δ) (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh)
    {J : Nat} (omega : Fin J → ↥C.centers) (pfx : Space) (A : ENNReal)
    (hfinite : ∀ q,
      IsKatzTaoAt A (selectedFamily D C omega)
        ((canonicalTestFamily hδ D C).testBody q)) :
    IsKatzTao A
      (FamilyStickyConvexBodyTranslationConcentrationV1.translateFamily
        (selectedFamily D C omega) pfx) := by
  rw [isKatzTao_iff_concentration_le]
  intro K
  have hall := selected_isKatzTao_of_preMotion_finite_tests
    hδ D C omega A hfinite
  have hlocal := (isKatzTao_iff_concentration_le.mp hall)
    (translateConvexBody K (-pfx))
  rw [← concentration_translateFamily
      (selectedFamily D C omega) (translateConvexBody K (-pfx)) pfx,
    translateConvexBody_neg_cancel] at hlocal
  exact hlocal
/-- Every canonical pre-motion test has each John side at least the source
radius; the stronger bound is `2 * δ`. -/
theorem delta_le_canonicalTestFamily_side
    (hδ : 0 < δ) (D : ActualTubeTestData δ tubeIndex)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh)
    (q : Fin (canonicalTestFamily hδ D C).testCard) (i : Fin 3) :
    δ ≤ (canonicalTestFamily hδ D C).side q i := by
  change δ ≤ (TubeCanonicalHullTests.positiveJohnData
    hδ (potentialTube D C) q).side i
  calc
    δ = 1 * δ := by simp
    _ ≤ 2 * δ := by gcongr; norm_num
    _ ≤ (TubeCanonicalHullTests.positiveJohnData
        hδ (potentialTube D C) q).side i :=
      JohnSideLowerFinal.boxCertificate_side_lower_of_tube_subset
        (potentialTube D C
          (TubeCanonicalHullTests.witnessIndex (potentialTube D C) q))
        (TubeCanonicalHullTests.witnessTube_subset_body
          (potentialTube D C) q)
        (TubeCanonicalHullTests.positiveJohnData
          hδ (potentialTube D C) q).certificate i


end FixedPackingPotentialFamily

namespace HierarchyPackingPlan

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]

/-- Packing certificates fixed at every hierarchy layer before any random
center or path is selected. -/
structure Plan
    (H : MultiscaleTubeHierarchy depth nominalRadius Index) where
  certificate : ∀ k : Fin depth,
    PackingCertificate
      (Metric.closedBall (0 : Space)
        (H.effectiveRadius (k.1 + 1) : Real))
      (H.effectiveRadius k.1)

/-- The existing maximal separated-set theorem supplies a canonical plan
from the source positivity hypotheses alone. -/
noncomputable def canonical
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H) : Plan H where
  certificate := fun k => Classical.choice
    (exists_motionBallPackingCertificate
      (H.effectiveRadius (k.1 + 1)) (H.effectiveRadius k.1)
      (G.childRadius_pos k))

variable (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (P : Plan H)

/-- Parent-local universal family of every translate available in the
preselected packing support. -/
def parentPotentialFamily (k : Fin depth) (p : Index (k.1 + 1)) :=
  FixedPackingPotentialFamily.potentialFamily
    (hierarchyFiberSeedData H k p) (P.certificate k)

/-- Parent-local fixed hull catalogue, constructed before the selector. -/
noncomputable def parentCanonicalTestFamily
    (G : HierarchyRandomMotionGeometry H)
    (k : Fin depth) (p : Index (k.1 + 1)) : BoxCertifiedTestFamily :=
  FixedPackingPotentialFamily.canonicalTestFamily
    (G.childRadius_pos k) (hierarchyFiberSeedData H k p) (P.certificate k)

@[simp] theorem parentCanonicalTestFamily_Cbox
    (G : HierarchyRandomMotionGeometry H)
    (k : Fin depth) (p : Index (k.1 + 1)) :
    (parentCanonicalTestFamily H P G k p).Cbox = 288 := rfl

@[simp] theorem parentCanonicalTestFamily_activeTests
    (G : HierarchyRandomMotionGeometry H)
    (k : Fin depth) (p : Index (k.1 + 1)) :
    (parentCanonicalTestFamily H P G k p).activeTests = Finset.univ := rfl

/-- The sole analytic input needed after the fixed packing tests, John
certificates, and transverse side bounds have been constructed internally. -/
structure MeanScaleData (G : HierarchyRandomMotionGeometry H) where
  branchingMeanScale : ∀ (k : Fin depth) (p : Index (k.1 + 1)),
    p ∈ (H.step k.1 k.2).combinatorics.index.coarse →
    ∀ K, K ∈ (parentCanonicalTestFamily H P G k p).activeTests →
      (297 *
        ((H.step k.1 k.2).combinatorics.branchingFactor : Real) *
        (((parentCanonicalTestFamily H P G k p).side K 0) : Real) *
        (((parentCanonicalTestFamily H P G k p).side K 1) : Real)) *
          ((H.effectiveRadius k.1 : Real) ^ 2 / 2) ≤
        (((((parentCanonicalTestFamily H P G k p).Cbox⁻¹ : NNReal) : Real) ^ 3 *
          ∏ i, (((parentCanonicalTestFamily H P G k p).side K i) : Real)) *
            (H.effectiveRadius (k.1 + 1) : Real) ^ 2)

/-- Replace an old test list by the fixed pre-motion hull catalogue in the
exact geometry type consumed by the hierarchy selector. -/

noncomputable def toPreMotionGeometry
    (G : HierarchyRandomMotionGeometry H) (M : MeanScaleData H P G) :
    HierarchyRandomMotionGeometry H where
  tests := parentCanonicalTestFamily H P G
  childRadius_pos := G.childRadius_pos
  childRadius_le_half := G.childRadius_le_half
  parentRadius_le_one := G.parentRadius_le_one
  childRadius_le_side_zero := by
    intro k p hp K hK
    exact FixedPackingPotentialFamily.delta_le_canonicalTestFamily_side
      (G.childRadius_pos k) (hierarchyFiberSeedData H k p)
      (P.certificate k) K 0
  childRadius_le_side_one := by
    intro k p hp K hK
    exact FixedPackingPotentialFamily.delta_le_canonicalTestFamily_side
      (G.childRadius_pos k) (hierarchyFiberSeedData H k p)
      (P.certificate k) K 1
  branchingMeanScale := M.branchingMeanScale

end HierarchyPackingPlan

namespace JointCertificateAdapter

variable {depth : Nat} {nominalRadius : Nat → NNReal}
  {Index : Nat → Type*}
  [∀ l, Fintype (Index l)] [∀ l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  (Q : HierarchyJointRandomMotionCertificate H G)

/-- The precise upstream coherence condition: the selector used the packing
certificate fixed by the pre-motion plan.  The joint output retains its
certificate, so no packing index is erased at this endpoint. -/
def UsesPackingPlan (P : HierarchyPackingPlan.Plan H) : Prop :=
  ∀ k, (Q.output.layerOutput k).certificate = P.certificate k

/-- Reading the retained certificates back from an existing joint output
produces a plan with definitional coherence.  This confirms that the joint
endpoint has not erased the finite packing index; only preselection staging is
missing from the upstream constructor. -/
def outputPackingPlan : HierarchyPackingPlan.Plan H where
  certificate := fun k => (Q.output.layerOutput k).certificate

@[simp] theorem uses_outputPackingPlan :
    UsesPackingPlan Q (outputPackingPlan Q) := fun _ => rfl

/-- Transport the selected center into the pre-motion plan's center type. -/
noncomputable def plannedOmega
    (P : HierarchyPackingPlan.Plan H)
    (hplan : UsesPackingPlan Q P) (k : Fin depth)
    (j : Fin (repetitions G.toDependentSource k)) :
    ↥(P.certificate k).centers :=
  ⟨((Q.output.layerOutput k).omega j).1, by
    have hg := ((Q.output.layerOutput k).omega j).2
    have hc : (Q.output.layerOutput k).certificate.centers =
        (P.certificate k).centers :=
      congrArg (fun C => C.centers) (hplan k)
    rwa [← hc]⟩

theorem plannedOmega_coe
    (P : HierarchyPackingPlan.Plan H)
    (hplan : UsesPackingPlan Q P) (k : Fin depth)
    (j : Fin (repetitions G.toDependentSource k)) :
    (((plannedOmega Q P hplan k j).1 : Space)) = Q.output.omega k j := rfl

/-- With only packing-plan coherence left upstream, the fixed parent-local
catalogue controls every selected center sequence and hence every convex
test, including after an arbitrary common hierarchy prefix. -/
theorem prefixFiber_isKatzTao_of_preMotion_finite_tests
    (P : HierarchyPackingPlan.Plan H)
    (hplan : UsesPackingPlan Q P)
    (path : Q.Path) (k : Fin depth) (p : Index (k.1 + 1))
    (A : ENNReal)
    (hfinite : ∀ q,
      IsKatzTaoAt A
        (FixedPackingPotentialFamily.selectedFamily
          (hierarchyFiberSeedData H k p) (P.certificate k)
          (plannedOmega Q P hplan k))
        ((HierarchyPackingPlan.parentCanonicalTestFamily H P G k p).testBody q)) :
    IsKatzTao A
      (FamilyStickyConvexBodyTranslationConcentrationV1.translateFamily
        (FixedPackingPotentialFamily.selectedFamily
          (hierarchyFiberSeedData H k p) (P.certificate k)
          (plannedOmega Q P hplan k))
        (Q.output.prefixVector path k)) := by
  exact FixedPackingPotentialFamily.prefixSelected_isKatzTao_of_preMotion_finite_tests
    (G.childRadius_pos k) (hierarchyFiberSeedData H k p)
    (P.certificate k) (plannedOmega Q P hplan k)
    (Q.output.prefixVector path k) A hfinite

end JointCertificateAdapter

#print axioms SupportedFiniteHullTests.isKatzTao_of_supported_finite_hull_tests
#print axioms FixedPackingPotentialFamily.selectedFamily_eq_potentialFamily_supportMap
#print axioms FixedPackingPotentialFamily.selected_isKatzTao_of_preMotion_finite_tests
#print axioms FixedPackingPotentialFamily.prefixSelected_isKatzTao_of_preMotion_finite_tests
#print axioms FixedPackingPotentialFamily.delta_le_canonicalTestFamily_side
#print axioms HierarchyPackingPlan.toPreMotionGeometry
#print axioms HierarchyPackingPlan.canonical
#print axioms HierarchyPackingPlan.parentCanonicalTestFamily
#print axioms JointCertificateAdapter.plannedOmega
#print axioms JointCertificateAdapter.plannedOmega_coe
#print axioms JointCertificateAdapter.prefixFiber_isKatzTao_of_preMotion_finite_tests

end
end FamilyStickyHierarchyPreMotionHullTestSupportV1
