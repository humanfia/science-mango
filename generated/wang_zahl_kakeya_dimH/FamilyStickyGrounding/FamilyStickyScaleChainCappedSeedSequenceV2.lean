import FamilyStickyGrounding.FamilyStickyScaleChainRelevantThetaCapInvariantV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainCappedSeedSequenceV2

open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleSequenceRefinesAtV2
open FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence
open FamilyStickyScaleSequenceInsertionTransportV2
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence
open FamilyStickyScaleChainRelevantThetaCapInvariantV2

noncomputable section

/-!
# A capped two-interval seed scale sequence

Starting from the one-interval sequence `1 -> delta`, insert an abstract
positive cap between the endpoints.  The resulting radii are literally

`1, cap, delta`.

If `delta^gap <= cap`, the top interval is large.  The only other interval
has upper endpoint exactly `cap`; hence every non-large interval has endpoint
at most `cap`.  The construction is independent of any later choice of a
uniform automatic normalized-terminal cap.
-/

variable {delta cap : NNReal} {gap : Real}

/-! ## The endpoint sequence and literal cap insertion -/

/-- The canonical one-interval scale sequence `1 -> delta`. -/
def endpointScaleSequence (delta : NNReal) (delta_le_one : delta <= 1) :
    FiniteScaleSequence delta 1 where
  radius i := if i = 0 then 1 else delta
  antitone_radius := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  top_eq := by simp
  bottom_eq := by simp

@[simp] theorem endpointScaleSequence_theta_zero
    (delta_le_one : delta <= 1) :
    (endpointScaleSequence delta delta_le_one).theta 0 = 1 := by
  rfl

@[simp] theorem endpointScaleSequence_tau_zero
    (delta_le_one : delta <= 1) :
    (endpointScaleSequence delta delta_le_one).tau 0 = delta := by
  rfl

/-- Insert `cap` into the unique interval, producing depth two. -/
def cappedSeedScaleSequence
    (delta_le_cap : delta <= cap) (cap_le_one : cap <= 1) :
    FiniteScaleSequence delta 2 :=
  let base := endpointScaleSequence delta (delta_le_cap.trans cap_le_one)
  insertRadius base (0 : Fin 1) cap
    (by change delta <= cap; exact delta_le_cap)
    (by change cap <= 1; exact cap_le_one)

/-- The canonical insertion certificate for the capped seed. -/
theorem cappedSeedScaleSequence_refinesAt
    (delta_le_cap : delta <= cap) (cap_le_one : cap <= 1) :
    let base := endpointScaleSequence delta (delta_le_cap.trans cap_le_one)
    ScaleSequenceRefinesAt base (0 : Fin 1) cap
      (cappedSeedScaleSequence delta_le_cap cap_le_one) := by
  dsimp only [cappedSeedScaleSequence]
  exact insertRadius_refinesAt
    (endpointScaleSequence delta (delta_le_cap.trans cap_le_one))
    (0 : Fin 1) cap (by change delta <= cap; exact delta_le_cap)
      (by change cap <= 1; exact cap_le_one)

@[simp] theorem cappedSeedScaleSequence_theta_zero
    (delta_le_cap : delta <= cap) (cap_le_one : cap <= 1) :
    (cappedSeedScaleSequence delta_le_cap cap_le_one).theta (0 : Fin 2) = 1 := by
  have href := cappedSeedScaleSequence_refinesAt delta_le_cap cap_le_one
  have h := theta_upperChild_eq href
  simpa [upperChildIndex] using h

@[simp] theorem cappedSeedScaleSequence_tau_zero
    (delta_le_cap : delta <= cap) (cap_le_one : cap <= 1) :
    (cappedSeedScaleSequence delta_le_cap cap_le_one).tau (0 : Fin 2) = cap := by
  have href := cappedSeedScaleSequence_refinesAt delta_le_cap cap_le_one
  have h := tau_upperChild_eq href
  simpa [upperChildIndex] using h

@[simp] theorem cappedSeedScaleSequence_theta_one
    (delta_le_cap : delta <= cap) (cap_le_one : cap <= 1) :
    (cappedSeedScaleSequence delta_le_cap cap_le_one).theta (1 : Fin 2) = cap := by
  have href := cappedSeedScaleSequence_refinesAt delta_le_cap cap_le_one
  have h := theta_lowerChild_eq href
  simpa [lowerChildIndex] using h

@[simp] theorem cappedSeedScaleSequence_tau_one
    (delta_le_cap : delta <= cap) (cap_le_one : cap <= 1) :
    (cappedSeedScaleSequence delta_le_cap cap_le_one).tau (1 : Fin 2) = delta := by
  have href := cappedSeedScaleSequence_refinesAt delta_le_cap cap_le_one
  have h := tau_lowerChild_eq href
  simpa [lowerChildIndex] using h

/-- The constructor has the promised literal three radii. -/
theorem cappedSeedScaleSequence_radii
    (delta_le_cap : delta <= cap) (cap_le_one : cap <= 1) :
    (cappedSeedScaleSequence delta_le_cap cap_le_one).radius (0 : Fin 3) = 1 /\
      (cappedSeedScaleSequence delta_le_cap cap_le_one).radius (1 : Fin 3) = cap /\
      (cappedSeedScaleSequence delta_le_cap cap_le_one).radius (2 : Fin 3) = delta := by
  constructor
  · exact cappedSeedScaleSequence_theta_zero delta_le_cap cap_le_one
  constructor
  · exact cappedSeedScaleSequence_tau_zero delta_le_cap cap_le_one
  · exact cappedSeedScaleSequence_tau_one delta_le_cap cap_le_one

/-! ## Top largeness and the whole-chain non-large cap -/

/-- The top interval `cap -> 1` is large under the exact displayed power
condition. -/
theorem cappedSeedScaleSequence_top_isLarge
    (delta_le_cap : delta <= cap) (cap_le_one : cap <= 1)
    (delta_power_le_cap : (delta : ENNReal) ^ gap <= (cap : ENNReal)) :
    (cappedSeedScaleSequence delta_le_cap cap_le_one).IsLarge gap (0 : Fin 2) := by
  unfold FiniteScaleSequence.IsLarge
  simpa using delta_power_le_cap

/-- Since the top interval is large and the remaining interval has upper
endpoint `cap`, the entire seed satisfies the exact relevant theta-cap
invariant. -/
theorem cappedSeedScaleSequence_nonLargeThetaCap
    (delta_le_cap : delta <= cap) (cap_le_one : cap <= 1)
    (delta_power_le_cap : (delta : ENNReal) ^ gap <= (cap : ENNReal)) :
    NonLargeThetaCap (cappedSeedScaleSequence delta_le_cap cap_le_one)
      gap cap := by
  intro m not_large
  fin_cases m
  · exact (not_large (cappedSeedScaleSequence_top_isLarge
      delta_le_cap cap_le_one delta_power_le_cap)).elim
  · simp

/-! ## One positive global delta threshold -/

/-- A single abstract-cap threshold enforcing both `delta <= cap` and
`delta^gap <= cap`. -/
def cappedSeedDeltaThreshold (cap : NNReal) (gap : Real) : NNReal :=
  min cap (cap ^ (1 / gap))

theorem cappedSeedDeltaThreshold_pos
    (cap_pos : 0 < cap) (gap : Real) :
    0 < cappedSeedDeltaThreshold cap gap := by
  rw [cappedSeedDeltaThreshold, lt_min_iff]
  exact ⟨cap_pos, NNReal.rpow_pos cap_pos⟩

theorem cappedSeedDeltaThreshold_le_cap
    (cap : NNReal) (gap : Real) :
    cappedSeedDeltaThreshold cap gap <= cap := by
  exact min_le_left _ _

theorem cappedSeedDeltaThreshold_le_one
    (cap_le_one : cap <= 1) (gap : Real) :
    cappedSeedDeltaThreshold cap gap <= 1 :=
  (cappedSeedDeltaThreshold_le_cap cap gap).trans cap_le_one

/-- The threshold automatically supplies the ordered endpoints and the top
large-power inequality. -/
theorem cappedSeedDeltaBounds_of_le_threshold
    (cap_pos : 0 < cap) (gap_pos : 0 < gap)
    (delta_le : delta <= cappedSeedDeltaThreshold cap gap) :
    delta <= cap /\ (delta : ENNReal) ^ gap <= (cap : ENNReal) := by
  have delta_le_cap : delta <= cap :=
    delta_le.trans (cappedSeedDeltaThreshold_le_cap cap gap)
  have delta_le_inverse : delta <= cap ^ (1 / gap) :=
    delta_le.trans (min_le_right _ _)
  have inverse_power :
      ((cap ^ (1 / gap) : NNReal) : ENNReal) ^ gap = (cap : ENNReal) := by
    rw [ENNReal.coe_rpow_of_ne_zero cap_pos.ne', <- ENNReal.rpow_mul]
    have exponent_eq : (1 / gap) * gap = (1 : Real) := by
      field_simp [ne_of_gt gap_pos]
    rw [exponent_eq, ENNReal.rpow_one]
  refine ⟨delta_le_cap, ?_⟩
  calc
    (delta : ENNReal) ^ gap <=
        ((cap ^ (1 / gap) : NNReal) : ENNReal) ^ gap := by
      apply ENNReal.rpow_le_rpow
      · exact_mod_cast delta_le_inverse
      · exact gap_pos.le
    _ = (cap : ENNReal) := inverse_power


/-- The threshold-specialized seed sequence.  The cap remains abstract. -/
def cappedSeedScaleSequenceOfThresholdPos
    (cap_pos : 0 < cap) (cap_le_one : cap <= 1) (gap_pos : 0 < gap)
    (delta_le : delta <= cappedSeedDeltaThreshold cap gap) :
    FiniteScaleSequence delta 2 :=
  cappedSeedScaleSequence
    (cappedSeedDeltaBounds_of_le_threshold cap_pos gap_pos delta_le).1
    cap_le_one

theorem cappedSeedScaleSequenceOfThresholdPos_nonLargeThetaCap
    (cap_pos : 0 < cap) (cap_le_one : cap <= 1) (gap_pos : 0 < gap)
    (delta_le : delta <= cappedSeedDeltaThreshold cap gap) :
    NonLargeThetaCap
      (cappedSeedScaleSequenceOfThresholdPos cap_pos cap_le_one gap_pos
        delta_le)
      gap cap := by
  let bounds := cappedSeedDeltaBounds_of_le_threshold cap_pos gap_pos delta_le
  exact cappedSeedScaleSequence_nonLargeThetaCap bounds.1 cap_le_one bounds.2

#print axioms endpointScaleSequence
#print axioms cappedSeedScaleSequence_refinesAt
#print axioms cappedSeedScaleSequence_radii
#print axioms cappedSeedScaleSequence_top_isLarge
#print axioms cappedSeedScaleSequence_nonLargeThetaCap
#print axioms cappedSeedDeltaThreshold_pos
#print axioms cappedSeedDeltaBounds_of_le_threshold
#print axioms cappedSeedScaleSequenceOfThresholdPos_nonLargeThetaCap

end
end FamilyStickyScaleChainCappedSeedSequenceV2
