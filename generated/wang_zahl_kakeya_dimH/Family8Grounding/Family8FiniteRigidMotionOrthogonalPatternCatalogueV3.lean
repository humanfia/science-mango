import Family8Grounding.Family8FiniteIncidencePatternSamplerV7
import Family8Grounding.Family8FiniteRigidMotionOrthogonalTwoCapLawV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalPatternCatalogueV3

open LeanEval.Analysis.WangZahlKakeya
open Family8FiniteRigidMotionOrthogonalHaarV4
open Family8FiniteRigidMotionOrthogonalTwoCapLawV2
open Family8FiniteIncidencePatternSamplerV7

noncomputable section

/-!
# A finite orthogonal catalogue preserving all prescribed cap incidences

For finitely many source directions and finitely many unit cap centres, apply
the generic incidence-pattern sampler to normalized Haar measure on O(3).
Every selected catalogue element is a literal orthogonal transformation, and
all two-cap counts obey the quadratic Haar bound simultaneously.
-/

variable {source center : Type*}
  [Fintype source] [DecidableEq source]
  [Fintype center] [DecidableEq center]

abbrev OrthogonalCapTest (source center : Type*) := source × center

def orthogonalCapEventFamily
    (direction : source -> Space) (capCenter : center -> Space)
    (cap : NNReal) :
    MeasurableEventFamily OrthogonalThree
      (OrthogonalCapTest source center) where
  event q := orthogonalTwoCapEvent (direction q.1) (capCenter q.2) cap
  measurable_event q :=
    measurableSet_orthogonalTwoCapEvent (direction q.1) (capCenter q.2) cap

abbrev OrthogonalPatternSample
    (direction : source -> Space) (capCenter : center -> Space)
    (cap : NNReal) (n : Nat) :=
  (orthogonalCapEventFamily direction capCenter cap).PatternSample
    orthogonalThreeHaarProbability n

def sampledOrthogonal
    (direction : source -> Space) (capCenter : center -> Space)
    (cap : NNReal) {n : Nat}
    (g : OrthogonalPatternSample direction capCenter cap n) :
    OrthogonalThree :=
  (orthogonalCapEventFamily direction capCenter cap).sampleRepresentative
    orthogonalThreeHaarProbability g

def sampledTwoCapFinset
    (direction : source -> Space) (capCenter : center -> Space)
    (cap : NNReal) (n : Nat) (q : OrthogonalCapTest source center) :
    Finset (OrthogonalPatternSample direction capCenter cap n) :=
  (orthogonalCapEventFamily direction capCenter cap).sampleEventFinset
    orthogonalThreeHaarProbability n q

theorem scale_le_card_orthogonalPatternSample
    (direction : source -> Space) (capCenter : center -> Space)
    (cap : NNReal) (n : Nat) :
    (n : Real) ≤
      Fintype.card (OrthogonalPatternSample direction capCenter cap n) := by
  exact (orthogonalCapEventFamily direction capCenter cap).scale_le_card_patternSample
    orthogonalThreeHaarProbability n

theorem card_sampledTwoCapFinset_le
    (direction : source -> Space) (capCenter : center -> Space)
    (hcenter : forall k, ‖capCenter k‖ = 1)
    (cap : NNReal) (hcap : 0 < cap) (hcapHalf : cap ≤ 1 / 2)
    (n : Nat) (q : OrthogonalCapTest source center) :
    ((sampledTwoCapFinset direction capCenter cap n q).card : Real) ≤
      (n : Real) * (10 * (cap : Real) ^ 2) +
        Fintype.card
          (Pattern (OrthogonalCapTest source center)) := by
  let F := orthogonalCapEventFamily direction capCenter cap
  have hsample :=
    F.card_sampleRepresentative_event_le_patternCard
      orthogonalThreeHaarProbability n q
  have hmass :
      orthogonalThreeHaarProbability.real (F.event q) ≤
        10 * (cap : Real) ^ 2 := by
    change
      (orthogonalThreeHaarProbability
        (orthogonalTwoCapEvent
          (direction q.1) (capCenter q.2) cap)).toReal ≤
        10 * (cap : Real) ^ 2
    exact orthogonalTwoCapEvent_toReal_le_ten_mul_sq
      (direction q.1) (capCenter q.2) (hcenter q.2)
      cap hcap hcapHalf
  calc
    ((sampledTwoCapFinset direction capCenter cap n q).card : Real) ≤
        (n : Real) * orthogonalThreeHaarProbability.real (F.event q) +
          Fintype.card
            (Pattern (OrthogonalCapTest source center)) := by
      simpa only [sampledTwoCapFinset, F] using hsample
    _ ≤ (n : Real) * (10 * (cap : Real) ^ 2) +
          Fintype.card
            (Pattern (OrthogonalCapTest source center)) := by
      gcongr

theorem card_sampledTwoCapFinset_le_card_mul_eleven_sq
    (direction : source -> Space) (capCenter : center -> Space)
    (hcenter : forall k, ‖capCenter k‖ = 1)
    (cap : NNReal) (hcap : 0 < cap) (hcapHalf : cap ≤ 1 / 2)
    (n : Nat)
    (hround :
      (Fintype.card
          (Pattern (OrthogonalCapTest source center)) : Real) ≤
        (n : Real) * (cap : Real) ^ 2)
    (q : OrthogonalCapTest source center) :
    ((sampledTwoCapFinset direction capCenter cap n q).card : Real) ≤
      (Fintype.card
          (OrthogonalPatternSample direction capCenter cap n) : Real) *
        (11 * (cap : Real) ^ 2) := by
  have hcount :=
    card_sampledTwoCapFinset_le direction capCenter hcenter
      cap hcap hcapHalf n q
  have hncard :=
    scale_le_card_orthogonalPatternSample direction capCenter cap n
  have hsq : 0 ≤ (cap : Real) ^ 2 := sq_nonneg _
  calc
    ((sampledTwoCapFinset direction capCenter cap n q).card : Real) ≤
        (n : Real) * (10 * (cap : Real) ^ 2) +
          Fintype.card
            (Pattern (OrthogonalCapTest source center)) := hcount
    _ ≤ (n : Real) * (11 * (cap : Real) ^ 2) := by
      nlinarith
    _ ≤ (Fintype.card
          (OrthogonalPatternSample direction capCenter cap n) : Real) *
          (11 * (cap : Real) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hncard (by positivity)

#print axioms scale_le_card_orthogonalPatternSample
#print axioms card_sampledTwoCapFinset_le
#print axioms card_sampledTwoCapFinset_le_card_mul_eleven_sq

end
end Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
