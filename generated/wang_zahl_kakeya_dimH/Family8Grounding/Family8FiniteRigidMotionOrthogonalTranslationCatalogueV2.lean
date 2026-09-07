import Family8Grounding.Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalTranslationCatalogueV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8FiniteIncidencePatternSamplerV7
open Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
open Family8FiniteRigidMotionOrthogonalHundredContainmentMeanV2
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2

noncomputable section

/-!
# Product catalogue of sampled rotations and arbitrary finite translations

The rotation catalogue controls every hundred-tube test for each fixed
translation. Summing the same bound over a finite translation type preserves
the identical relative quadratic cap for the full product catalogue.
-/

variable {source translation : Type*}
  [Fintype source] [DecidableEq source]
  [Fintype translation] [DecidableEq translation]
  {delta : NNReal}

abbrev HundredRigidSample
    (translation : Type*)
    (T : source -> Tube delta) (hdelta : 0 < delta) (n : Nat) :=
  translation × HundredOrthogonalSample T hdelta n

def sampledHundredRigidContainmentFinset
    (T : source -> Tube delta) (hdelta : 0 < delta) (n : Nat)
    (translationVector : translation -> Space)
    (i : source) (W : Tube delta) :
    Finset (HundredRigidSample translation T hdelta n) :=
  @Finset.filter (HundredRigidSample translation T hdelta n)
    (fun g =>
      sampledHundredOrthogonal T hdelta g.2 ∈
        orthogonalHundredContainmentEvent
          (T i) W (translationVector g.1))
    (fun g => Classical.propDecidable
      (sampledHundredOrthogonal T hdelta g.2 ∈
        orthogonalHundredContainmentEvent
          (T i) W (translationVector g.1)))
    Finset.univ

theorem card_sampledHundredRigidContainmentFinset_eq_sum
    (T : source -> Tube delta) (hdelta : 0 < delta) (n : Nat)
    (translationVector : translation -> Space)
    (i : source) (W : Tube delta) :
    (sampledHundredRigidContainmentFinset
        T hdelta n translationVector i W).card =
      ∑ t : translation,
        (sampledHundredContainmentFinset
          T hdelta n i W (translationVector t)).card := by
  classical
  unfold sampledHundredRigidContainmentFinset
    sampledHundredContainmentFinset
  rw [Finset.card_eq_sum_ones]
  rw [← Finset.univ_product_univ, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem card_sampledHundredRigidContainmentFinset_le
    (T : source -> Tube delta) (hdelta : 0 < delta)
    (henlargedHalf : enlargedHundredDirectionCap delta ≤ 1 / 2)
    (n : Nat)
    (hround :
      (Fintype.card
          (Pattern
            (OrthogonalCapTest source
              (HundredDirectionChoice delta hdelta))) : Real) ≤
        (n : Real) * (enlargedHundredDirectionCap delta : Real) ^ 2)
    (translationVector : translation -> Space)
    (i : source) (W : Tube delta) :
    ((sampledHundredRigidContainmentFinset
        T hdelta n translationVector i W).card : Real) ≤
      (Fintype.card
          (HundredRigidSample translation T hdelta n) : Real) *
        (11 * (enlargedHundredDirectionCap delta : Real) ^ 2) := by
  classical
  have hsplit :=
    card_sampledHundredRigidContainmentFinset_eq_sum
      T hdelta n translationVector i W
  have hsplitReal :
      ((sampledHundredRigidContainmentFinset
          T hdelta n translationVector i W).card : Real) =
        ∑ t : translation,
          ((sampledHundredContainmentFinset
            T hdelta n i W (translationVector t)).card : Real) := by
    exact_mod_cast hsplit
  rw [hsplitReal]
  calc
    (∑ t : translation,
        ((sampledHundredContainmentFinset
          T hdelta n i W (translationVector t)).card : Real)) ≤
        ∑ _t : translation,
          (Fintype.card (HundredOrthogonalSample T hdelta n) : Real) *
            (11 * (enlargedHundredDirectionCap delta : Real) ^ 2) := by
      exact Finset.sum_le_sum fun t _ht =>
        card_sampledHundredContainmentFinset_le
          T hdelta henlargedHalf n hround i W (translationVector t)
    _ = (Fintype.card
          (HundredRigidSample translation T hdelta n) : Real) *
          (11 * (enlargedHundredDirectionCap delta : Real) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        HundredRigidSample, Fintype.card_prod, Nat.cast_mul]
      ring

#print axioms card_sampledHundredRigidContainmentFinset_eq_sum
#print axioms card_sampledHundredRigidContainmentFinset_le

end
end Family8FiniteRigidMotionOrthogonalTranslationCatalogueV2
