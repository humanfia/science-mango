import FamilyStickyGrounding.FamilyStickyActualTubeTranslationV1
import FamilyStickyGrounding.FamilyStickyRandomTranslationGridAdapterV1

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualTubeTranslationGridV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyRandomFiniteChernoffV3
open FamilyStickyRandomTranslationIncidenceV1
open FamilyStickyRandomTranslationGridAdapterV1

noncomputable section

/-!
# An actual finite translation grid for repository tubes

Test bodies are indexed by `Fin testCard`; this preserves repetitions and
keeps the finite union bound decidable.  A grid hit is the literal geometric
statement that the carrier of the actually translated tube is contained in
the indexed convex test body.
-/

structure ActualTubeTranslationGrid
    (delta : NNReal) (translation tubeIndex : Type*)
    [Fintype translation] [DecidableEq translation]
    [DecidableEq tubeIndex] where
  gridVector : translation -> Space
  tubes : Finset tubeIndex
  tube : tubeIndex -> Tube delta
  testCard : Nat
  testBody : Fin testCard -> ConvexBody Space
  activeTests : Finset (Fin testCard)

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- Literal single-translation load in one actual convex test body. -/
def singleLoad (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (g : translation) : Nat := by
  classical
  exact (G.tubes.filter fun i =>
    (translateTube (G.tube i) (G.gridVector g)).carrier ⊆
      (G.testBody K : Set Space)).card

/-- Literal number of grid translations moving one tube into one test body. -/
def tubeHitCount (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (i : tubeIndex) : Nat := by
  classical
  exact (Finset.univ.filter fun g =>
    (translateTube (G.tube i) (G.gridVector g)).carrier ⊆
      (G.testBody K : Set Space)).card

/-- Forget only the geometric implementation of a hit, retaining it as the
Boolean incidence relation consumed by the finite Chernoff engine. -/
def toIncidenceModel
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    TranslationIncidenceModel translation tubeIndex (Fin G.testCard) := by
  classical
  exact
    { tubes := G.tubes
      tests := G.activeTests
      hits := fun g i K => decide
        ((translateTube (G.tube i) (G.gridVector g)).carrier ⊆
          (G.testBody K : Set Space)) }

@[simp] theorem toIncidenceModel_tubes
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    G.toIncidenceModel.tubes = G.tubes := rfl

@[simp] theorem toIncidenceModel_tests
    (G : ActualTubeTranslationGrid delta translation tubeIndex) :
    G.toIncidenceModel.tests = G.activeTests := rfl

/-- The abstract load is definitionally the actual contained translated-tube
count. -/
theorem toIncidenceModel_loadNat
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (g : translation) :
    G.toIncidenceModel.loadNat K g = G.singleLoad K g := by
  classical
  simp [TranslationIncidenceModel.loadNat, toIncidenceModel, singleLoad]

/-- The abstract per-tube incidence number is the actual grid hit count. -/
theorem toIncidenceModel_gridHitsTube
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (i : tubeIndex) :
    G.toIncidenceModel.gridHitsTube K i = G.tubeHitCount K i := by
  classical
  simp [TranslationIncidenceModel.gridHitsTube, toIncidenceModel,
    tubeHitCount]

/-- The real load used in exponential moments is the cast of the literal
actual translated-tube count. -/
theorem toIncidenceModel_load
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (g : translation) :
    G.toIncidenceModel.load K g = (G.singleLoad K g : Real) := by
  rw [TranslationIncidenceModel.load, G.toIncidenceModel_loadNat]

/-- Simultaneously good actual translations, reduced only to geometric grid
incidence caps and the explicit finite Chernoff numerical inequality. -/
theorem exists_grid_translations_singleLoad_le
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (translationBudget : Fin G.testCard -> Nat) (repetitions : Nat)
    {cap mean lambda threshold : Real}
    (hcap : 0 < cap) (hlambda : 0 <= lambda)
    (hloadCap : forall K, K ∈ G.activeTests -> forall g,
      (G.singleLoad K g : Real) <= cap)
    (hgrid : forall K, K ∈ G.activeTests -> forall i, i ∈ G.tubes ->
      G.tubeHitCount K i <= translationBudget K)
    (hbalance : forall K, K ∈ G.activeTests ->
      (G.tubes.card : Real) * (translationBudget K : Real) <=
        (Fintype.card translation : Real) * mean)
    (hnumerical :
      (G.activeTests.card : Real) *
          ((Fintype.card translation : Real) *
            (1 + (mean / cap) *
              (Real.exp (lambda * cap) - 1))) ^ repetitions <
        ((Finset.univ : Finset (Fin repetitions -> translation)).card : Real) *
          Real.exp (lambda * threshold)) :
    exists omega : Fin repetitions -> translation,
      forall K, K ∈ G.activeTests ->
        (∑ j, (G.singleLoad K (omega j) : Real)) <= threshold := by
  have h :=
    TranslationIncidenceModel.exists_product_choice_load_le_of_gridIncidence
      G.toIncidenceModel translationBudget repetitions hcap hlambda
      (fun K hK g => by
        rw [G.toIncidenceModel_load]
        exact hloadCap K hK g)
      (fun K hK i hi => by
        rw [G.toIncidenceModel_gridHitsTube]
        exact hgrid K hK i hi)
      hbalance hnumerical
  obtain ⟨omega, homega⟩ := h
  refine ⟨omega, ?_⟩
  intro K hK
  simpa [productLoad, G.toIncidenceModel_load] using homega K hK

#print axioms toIncidenceModel_loadNat
#print axioms toIncidenceModel_gridHitsTube
#print axioms toIncidenceModel_load
#print axioms exists_grid_translations_singleLoad_le

end ActualTubeTranslationGrid

end

end FamilyStickyActualTubeTranslationGridV1
