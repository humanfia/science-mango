import ArchonPhysics.TruncatedGaussianIIDMassSequence

/-!
# Positivity obstruction for untruncated iid Gaussian masses

A nondegenerate real Gaussian is not a physically admissible mass law: it
assigns positive probability to nonpositive masses.  More generally, if the
one-site probability of strict positivity is `p < 1`, then the probability
that the first `N` iid coordinates are all positive is exactly `p ^ N` and
tends to zero.  Consequently an infinite iid chain is strictly positive at
every site only on a null set.

This is a probability-theoretic obstruction only.  It makes no dynamical,
localization, kinetic-limit, or thermalization assertion.
-/

namespace ArchonPhysics.GaussianIIDMassPositivityObstruction

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The event that the first `N` coordinates of an indexed mass family are
strictly positive. -/
def finiteAllPositiveEvent {Omega : Type*} (mass : Nat → Omega → Real)
    (N : Nat) : Set Omega :=
  ⋂ n ∈ Finset.range N, mass n ⁻¹' Ioi 0

/-- The event that every coordinate of a countably infinite mass family is
strictly positive. -/
def infiniteAllPositiveEvent {Omega : Type*} (mass : Nat → Omega → Real) :
    Set Omega :=
  ⋂ n, mass n ⁻¹' Ioi 0

/-- For iid coordinates with common law `mu`, the probability that the first
`N` masses are all positive is exactly the `N`th power of the one-site
positivity probability. -/
theorem finiteAllPositiveEvent_measure_eq_pow
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (mu : Measure Real) (mass : Nat → Omega → Real)
    (hIndep : iIndepFun mass P) (hLaw : ∀ n, HasLaw (mass n) mu P)
    (N : Nat) :
    P (finiteAllPositiveEvent mass N) = (mu (Ioi 0)) ^ N := by
  rw [finiteAllPositiveEvent,
    hIndep.measure_inter_preimage_eq_mul (Finset.range N)
      (fun _ _ ↦ measurableSet_Ioi)]
  have hcoordinate (n : Nat) : P (mass n ⁻¹' Ioi 0) = mu (Ioi 0) := by
    change P {omega | 0 < mass n omega} = mu {x | 0 < x}
    exact (hLaw n).measure_eq measurableSet_Ioi
  simp_rw [hcoordinate]
  simp

/-- If one coordinate is positive with probability strictly below one, the
probability that the first `N` iid coordinates are all positive tends to
zero as `N → ∞`. -/
theorem finiteAllPositiveEvent_measure_tendsto_zero
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (mu : Measure Real) (mass : Nat → Omega → Real)
    (hIndep : iIndepFun mass P) (hLaw : ∀ n, HasLaw (mass n) mu P)
    (hPositiveLtOne : mu (Ioi 0) < 1) :
    Tendsto (fun N : Nat ↦ P (finiteAllPositiveEvent mass N)) atTop (nhds 0) := by
  simpa only [finiteAllPositiveEvent_measure_eq_pow P mu mass hIndep hLaw] using
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hPositiveLtOne

/-- Under the same strict one-site loss of positivity, an infinite iid chain
is positive at every site only on a null set. -/
theorem infiniteAllPositiveEvent_measure_eq_zero
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (mu : Measure Real) (mass : Nat → Omega → Real)
    (hIndep : iIndepFun mass P) (hLaw : ∀ n, HasLaw (mass n) mu P)
    (hPositiveLtOne : mu (Ioi 0) < 1) :
    P (infiniteAllPositiveEvent mass) = 0 := by
  apply le_antisymm
  · apply ge_of_tendsto'
      (finiteAllPositiveEvent_measure_tendsto_zero
        P mu mass hIndep hLaw hPositiveLtOne)
    intro N
    apply measure_mono
    intro omega homega
    simp only [infiniteAllPositiveEvent, mem_iInter, mem_preimage, mem_Ioi] at homega
    simp only [finiteAllPositiveEvent, mem_iInter, mem_preimage, mem_Ioi]
    exact fun n _hn ↦ homega n
  · exact bot_le

/-! ## Nondegenerate real Gaussians -/

/-- A nondegenerate real Gaussian gives positive mass to a negative open
interval. -/
theorem gaussianReal_negative_interval_pos (mean : Real) {variance : NNReal}
    (hVariance : variance ≠ 0) :
    0 < gaussianReal mean variance (Ioo (-1) 0) := by
  have hVolume : 0 < (volume : Measure Real) (Ioo (-1) 0) := by
    simp [Real.volume_Ioo]
  exact (gaussianReal_absolutelyContinuous' mean hVariance).pos_mono hVolume

/-- The strict-positivity probability of every nondegenerate real Gaussian is
strictly below one. -/
theorem gaussianReal_positive_probability_lt_one (mean : Real)
    {variance : NNReal} (hVariance : variance ≠ 0) :
    gaussianReal mean variance (Ioi 0) < 1 := by
  let G : Measure Real := gaussianReal mean variance
  have hNegative : 0 < G ((Ioi 0)ᶜ) := by
    have hSubset : Ioo (-1 : Real) 0 ⊆ (Ioi 0)ᶜ := by
      intro x hx
      simp only [mem_compl_iff, mem_Ioi, not_lt]
      exact hx.2.le
    exact (gaussianReal_negative_interval_pos mean hVariance).trans_le
      (measure_mono hSubset)
  have hComplement : G ((Ioi 0)ᶜ) = 1 - G (Ioi 0) := by
    rw [measure_compl measurableSet_Ioi (measure_ne_top G (Ioi 0))]
    simp only [measure_univ]
  rw [hComplement] at hNegative
  exact tsub_pos_iff_lt.mp hNegative

/-- Therefore an iid family with a common nondegenerate real-Gaussian law is
positive at every site only on a null set. -/
theorem gaussianIID_infiniteAllPositiveEvent_measure_eq_zero
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (mass : Nat → Omega → Real) (mean : Real) {variance : NNReal}
    (hVariance : variance ≠ 0) (hIndep : iIndepFun mass P)
    (hLaw : ∀ n, HasLaw (mass n) (gaussianReal mean variance) P) :
    P (infiniteAllPositiveEvent mass) = 0 :=
  infiniteAllPositiveEvent_measure_eq_zero P (gaussianReal mean variance)
    mass hIndep hLaw (gaussianReal_positive_probability_lt_one mean hVariance)

end

end ArchonPhysics.GaussianIIDMassPositivityObstruction
