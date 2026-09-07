import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Family8FiniteProbabilityCeilRoundingV1

noncomputable section

/-!
# Ceiling discretization of a finite probability law

For a probability measure on a finite discrete type, copy each atom
`ceil (n * mass)` times.  The resulting literal finite sample has at least
`n` elements, while the count over any set is at most its expected `n`-mass
plus one rounding unit per atom in that set.  This deterministic construction
is the finite-catalogue bridge used after pushing Haar measure to the finite
Boolean incidence-pattern type.
-/

variable {atom : Type*} [Fintype atom] [DecidableEq atom]
  [MeasurableSpace atom] [MeasurableSingletonClass atom]
  (mu : Measure atom) [IsProbabilityMeasure mu]

def ceilMultiplicity (n : Nat) (a : atom) : Nat :=
  Nat.ceil ((n : Real) * mu.real {a})

abbrev CeilSample (n : Nat) :=
  Sigma (fun a : atom => Fin (ceilMultiplicity mu n a))

def ceilSampleValue {n : Nat} (g : CeilSample mu n) : atom :=
  g.1

theorem scaled_atomMass_le_ceilMultiplicity
    (n : Nat) (a : atom) :
    (n : Real) * mu.real {a} <=
      (ceilMultiplicity mu n a : Real) := by
  exact Nat.le_ceil _

theorem ceilMultiplicity_le_scaled_atomMass_add_one
    (n : Nat) (a : atom) :
    (ceilMultiplicity mu n a : Real) <=
      (n : Real) * mu.real {a} + 1 := by
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem scale_le_sum_ceilMultiplicity (n : Nat) :
    (n : Real) <=
      ∑ a : atom, (ceilMultiplicity mu n a : Real) := by
  calc
    (n : Real) = (n : Real) * mu.real Set.univ := by simp
    _ = (n : Real) * (∑ a : atom, mu.real {a}) := by
      rw [sum_measureReal_singleton (μ := mu) Finset.univ]
      simp
    _ = ∑ a : atom, ((n : Real) * mu.real {a}) := by
      rw [Finset.mul_sum]
    _ <= ∑ a : atom, (ceilMultiplicity mu n a : Real) := by
      exact Finset.sum_le_sum
        (fun a _ => scaled_atomMass_le_ceilMultiplicity mu n a)

theorem sum_ceilMultiplicity_le_scaled_measure_add_card
    (n : Nat) (s : Finset atom) :
    ∑ a ∈ s, (ceilMultiplicity mu n a : Real) <=
      (n : Real) * mu.real (s : Set atom) + s.card := by
  calc
    ∑ a ∈ s, (ceilMultiplicity mu n a : Real) <=
        ∑ a ∈ s, ((n : Real) * mu.real {a} + 1) := by
      exact Finset.sum_le_sum
        (fun a _ => ceilMultiplicity_le_scaled_atomMass_add_one mu n a)
    _ = (n : Real) * (∑ a ∈ s, mu.real {a}) + s.card := by
      rw [Finset.mul_sum]
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        mul_one]
    _ = (n : Real) * mu.real (s : Set atom) + s.card := by
      rw [sum_measureReal_singleton (μ := mu) s]

theorem card_ceilSample (n : Nat) :
    Fintype.card (CeilSample mu n) =
      ∑ a : atom, ceilMultiplicity mu n a := by
  simp [CeilSample]

theorem scale_le_card_ceilSample (n : Nat) :
    (n : Real) <= (Fintype.card (CeilSample mu n) : Real) := by
  rw [card_ceilSample, Nat.cast_sum]
  exact scale_le_sum_ceilMultiplicity mu n

theorem card_ceilSample_filter
    (n : Nat) (s : Finset atom) :
    (Finset.univ.filter
        (fun g : CeilSample mu n => ceilSampleValue mu g ∈ s)).card =
      ∑ a ∈ s, ceilMultiplicity mu n a := by
  classical
  rw [Finset.card_filter]
  rw [Fintype.sum_sigma]
  calc
    (∑ a : atom,
        ∑ _y : Fin (ceilMultiplicity mu n a),
          if a ∈ s then 1 else 0) =
        ∑ a : atom,
          if a ∈ s then ceilMultiplicity mu n a else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases ha : a ∈ s <;> simp [ha]
    _ = ∑ a ∈ s, ceilMultiplicity mu n a := by
      simpa using
        (Finset.sum_filter (s := (Finset.univ : Finset atom))
          (p := fun a => a ∈ s)
          (f := fun a => ceilMultiplicity mu n a)).symm

theorem card_ceilSample_filter_le_scaled_measure_add_card
    (n : Nat) (s : Finset atom) :
    ((Finset.univ.filter
        (fun g : CeilSample mu n => ceilSampleValue mu g ∈ s)).card :
          Real) <=
      (n : Real) * mu.real (s : Set atom) + s.card := by
  rw [card_ceilSample_filter, Nat.cast_sum]
  exact sum_ceilMultiplicity_le_scaled_measure_add_card mu n s

#print axioms scaled_atomMass_le_ceilMultiplicity
#print axioms ceilMultiplicity_le_scaled_atomMass_add_one
#print axioms scale_le_sum_ceilMultiplicity
#print axioms sum_ceilMultiplicity_le_scaled_measure_add_card
#print axioms card_ceilSample
#print axioms scale_le_card_ceilSample
#print axioms card_ceilSample_filter
#print axioms card_ceilSample_filter_le_scaled_measure_add_card

end
end Family8FiniteProbabilityCeilRoundingV1
