import ArchonPhysics.GaussianIIDMassPositivityObstruction

/-!
# Acceptance target: untruncated Gaussian masses are not positive chains

For the concrete countable product of unit-mean, variance `1 / 100` real
Gaussians, the first-`N` positivity probability is an exact power tending to
zero, and the event that every mass is positive is null.
-/

namespace ArchonPhysicsConsumers.Thermalization

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal ProbabilityTheory
open ArchonPhysics.GaussianIIDMassPositivityObstruction

noncomputable section

namespace GaussianIIDMassPositivityObstruction

/-- A concrete nonzero Gaussian variance. -/
def variance : NNReal := 1 / 100

theorem variance_ne_zero : variance ≠ 0 := by
  norm_num [variance]

/-- Canonical untruncated iid Gaussian mass sequences. -/
abbrev SampleSpace := Nat → Real

def probability : Measure SampleSpace :=
  Measure.infinitePi (fun _ : Nat ↦ gaussianReal 1 variance)

noncomputable instance probability.instIsProbabilityMeasure :
    IsProbabilityMeasure probability := by
  unfold probability
  infer_instance

def massAt (n : Nat) : SampleSpace → Real := fun sample ↦ sample n

theorem massAt_hasLaw (n : Nat) :
    HasLaw (massAt n) (gaussianReal 1 variance) probability :=
  (measurePreserving_eval_infinitePi
    (fun _ : Nat ↦ gaussianReal 1 variance) n).hasLaw

theorem massAt_iIndep : iIndepFun massAt probability := by
  exact iIndepFun_infinitePi
    (P := fun _ : Nat ↦ gaussianReal 1 variance)
    (X := fun _ (mass : Real) ↦ mass) (fun _ ↦ measurable_id)

/-- Executable acceptance statement for the finite-power decay and the
infinite-chain null obstruction. -/
theorem problem_gaussian_iid_mass_positivity_obstruction :
    gaussianReal 1 variance (Ioi 0) < 1 ∧
      (∀ N, probability (finiteAllPositiveEvent massAt N) =
        (gaussianReal 1 variance (Ioi 0)) ^ N) ∧
      Tendsto (fun N : Nat ↦ probability (finiteAllPositiveEvent massAt N))
        atTop (nhds 0) ∧
      probability (infiniteAllPositiveEvent massAt) = 0 := by
  have hPositiveLtOne : gaussianReal 1 variance (Ioi 0) < 1 :=
    gaussianReal_positive_probability_lt_one 1 variance_ne_zero
  exact ⟨hPositiveLtOne,
    finiteAllPositiveEvent_measure_eq_pow probability
      (gaussianReal 1 variance) massAt massAt_iIndep massAt_hasLaw,
    finiteAllPositiveEvent_measure_tendsto_zero probability
      (gaussianReal 1 variance) massAt massAt_iIndep massAt_hasLaw hPositiveLtOne,
    gaussianIID_infiniteAllPositiveEvent_measure_eq_zero probability massAt 1
      variance_ne_zero massAt_iIndep massAt_hasLaw⟩

#print axioms problem_gaussian_iid_mass_positivity_obstruction

end GaussianIIDMassPositivityObstruction

end

end ArchonPhysicsConsumers.Thermalization
