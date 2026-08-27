import ArchonPhysics.TruncatedGaussianMassLaw

/-!
# Infinite iid sequence of positive truncated-Gaussian masses

This module takes the one-coordinate law from
`ArchonPhysics.TruncatedGaussianMassLaw` and constructs its countable product
with Mathlib's `Measure.infinitePi`.  The coordinate projections have the
prescribed law and are mutually independent.  All raw coordinates lie in the
frozen positive support simultaneously almost surely.

For consumers requiring positivity at every sample rather than almost surely,
we also provide a coordinatewise clipped representative.  It agrees with the
raw sequence almost surely, retains the same marginal laws and independence,
and lies in `[4/5,6/5]` pointwise.

No equivalence of infinite product measures is asserted here: finite-dimensional
mutual absolute continuity does not by itself imply equivalence of countable
products.  This module also makes no strong-law or thermalization assertion.
-/

namespace ArchonPhysics.TruncatedGaussianIIDMassSequence

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

open RandomEnsemble TruncatedGaussianMassLaw

/-- Infinite raw mass sequences. -/
abbrev SampleSpace := Nat → Real

/-- Countable product of one fixed truncated-Gaussian mass law. -/
def probability (parameters : Parameters) : Measure SampleSpace :=
  Measure.infinitePi (fun _ : Nat ↦ coordinateLaw parameters)

noncomputable instance probability.instIsProbabilityMeasure
    (parameters : Parameters) : IsProbabilityMeasure (probability parameters) := by
  unfold probability
  infer_instance

/-- Raw coordinate projection on the countable product space. -/
def rawMassAt (n : Nat) : SampleSpace → Real := fun sample ↦ sample n

theorem measurable_rawMassAt (n : Nat) : Measurable (rawMassAt n) := by
  unfold rawMassAt
  fun_prop

/-- Every coordinate projection has exactly the prescribed one-site law. -/
theorem rawMassAt_hasLaw (parameters : Parameters) (n : Nat) :
    HasLaw (rawMassAt n) (coordinateLaw parameters) (probability parameters) :=
  (measurePreserving_eval_infinitePi
    (fun _ : Nat ↦ coordinateLaw parameters) n).hasLaw

/-- The raw coordinate projections are mutually independent. -/
theorem rawMassCoordinates_iIndep (parameters : Parameters) :
    iIndepFun rawMassAt (probability parameters) := by
  exact ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : Nat ↦ coordinateLaw parameters)
    (X := fun _ (mass : Real) ↦ mass) (fun _ ↦ measurable_id)

/-- Each raw coordinate belongs to the compact positive mass support almost
surely. -/
theorem rawMassAt_mem_support_ae (parameters : Parameters) (n : Nat) :
    ∀ᵐ sample ∂probability parameters, rawMassAt n sample ∈ massSupport := by
  apply ((rawMassAt_hasLaw parameters n).ae_iff ?_).2
  · exact mem_massSupport_ae parameters
  · apply MeasurableSet.mem
    exact (show MeasurableSet massSupport from measurableSet_Icc)

/-- Outside one product-null set, all countably many raw coordinates belong to
the compact positive mass support simultaneously. -/
theorem rawMassSequence_mem_support_ae (parameters : Parameters) :
    ∀ᵐ sample ∂probability parameters,
      ∀ n, rawMassAt n sample ∈ massSupport :=
  ae_all_iff.mpr (rawMassAt_mem_support_ae parameters)

/-! ## A pointwise-positive representative -/

/-- Coordinatewise clipping gives an everywhere admissible positive mass. -/
def massAt (n : Nat) : SampleSpace → Real :=
  fun sample ↦ RandomEnsemble.clippedMass (rawMassAt n sample)

theorem measurable_massAt (n : Nat) : Measurable (massAt n) := by
  unfold massAt
  exact RandomEnsemble.measurable_clippedMass.comp (measurable_rawMassAt n)

theorem massAt_mem_support (n : Nat) (sample : SampleSpace) :
    massAt n sample ∈ massSupport :=
  RandomEnsemble.clippedMass_mem_support _

theorem massAt_pos (n : Nat) (sample : SampleSpace) : 0 < massAt n sample :=
  RandomEnsemble.clippedMass_pos _

/-- Clipping changes no coordinate outside a null set. -/
theorem massAt_eq_rawMassAt_ae (parameters : Parameters) (n : Nat) :
    massAt n =ᵐ[probability parameters] rawMassAt n := by
  filter_upwards [rawMassAt_mem_support_ae parameters n] with sample hsample
  exact RandomEnsemble.clippedMass_eq_self hsample

/-- Every pointwise-positive representative keeps the truncated-Gaussian law. -/
theorem massAt_hasLaw (parameters : Parameters) (n : Nat) :
    HasLaw (massAt n) (coordinateLaw parameters) (probability parameters) :=
  (rawMassAt_hasLaw parameters n).congr (massAt_eq_rawMassAt_ae parameters n)

/-- Coordinatewise measurable clipping preserves mutual independence. -/
theorem massCoordinates_iIndep (parameters : Parameters) :
    iIndepFun massAt (probability parameters) := by
  have hindep := (rawMassCoordinates_iIndep parameters).comp
    (fun _ : Nat ↦ RandomEnsemble.clippedMass)
    (fun _ ↦ RandomEnsemble.measurable_clippedMass)
  change iIndepFun
    (fun n ↦ RandomEnsemble.clippedMass ∘ rawMassAt n)
    (probability parameters)
  exact hindep

end

end ArchonPhysics.TruncatedGaussianIIDMassSequence
