import Mathlib

/-!
# Probabilistic interfaces for transferring a thermalization-time law

This module contains only measure-theoretic and asymptotic interfaces.  An
`equilibrationTime` is supplied as data; no microscopic-to-kinetic limit or
thermalization assertion is assumed or proved here.

The scaled time remains `ENNReal` throughout.  In particular, a non-occurring
event stays at `⊤` instead of being silently changed to zero by `ENNReal.toReal`.
-/

namespace ArchonPhysics.ThermalizationTransfer

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

/-- A coupled large-volume, weak-coupling limit above a supplied size cutoff. -/
structure AdmissibleJointLimit (sizeCutoff : Real → Nat) where
  /-- System size along the limit. -/
  systemSize : Nat → Nat
  /-- Positive effective coupling along the limit. -/
  coupling : Nat → Real
  /-- The weak coupling is positive at every index. -/
  coupling_pos : ∀ j, 0 < coupling j
  /-- The coupling tends to zero from the positive side. -/
  coupling_tendsto_zero :
    Tendsto coupling atTop (nhdsWithin 0 (Ioi 0))
  /-- The system size tends to infinity. -/
  systemSize_tendsto_atTop : Tendsto systemSize atTop atTop
  /-- Eventually the volume lies in the admitted finite-size regime. -/
  eventually_sizeCutoff :
    ∀ᶠ j in atTop, sizeCutoff (coupling j) ≤ systemSize j

/-- The kinetic scaling `g² T`, kept in `ENNReal` so that `T = ⊤` is retained. -/
def scaledEquilibrationTime {Ω : Type*}
    (equilibrationTime : Nat → Real → Ω → ENNReal)
    (N : Nat) (g : Real) (ω : Ω) : ENNReal :=
  ENNReal.ofReal (g ^ 2) * equilibrationTime N g ω

/-- The scaled time is measurable whenever the supplied equilibration time is measurable. -/
theorem measurable_scaledEquilibrationTime {Ω : Type*} [MeasurableSpace Ω]
    (equilibrationTime : Nat → Real → Ω → ENNReal) (N : Nat) (g : Real)
    (hT : Measurable (equilibrationTime N g)) :
    Measurable (scaledEquilibrationTime equilibrationTime N g) := by
  exact measurable_const.mul hT

/-- At nonzero coupling, kinetic scaling preserves a non-occurring (`⊤`) hit. -/
theorem scaledEquilibrationTime_eq_top_iff {Ω : Type*}
    (equilibrationTime : Nat → Real → Ω → ENNReal)
    (N : Nat) (g : Real) (ω : Ω) (hg : g ≠ 0) :
    scaledEquilibrationTime equilibrationTime N g ω = ⊤ ↔
      equilibrationTime N g ω = ⊤ := by
  have hfactor_ne_zero : ENNReal.ofReal (g ^ 2) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_ne_zero hg)
  have hfactor_ne_top : ENNReal.ofReal (g ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [scaledEquilibrationTime, ENNReal.mul_eq_top]
  simp [hfactor_ne_zero, hfactor_ne_top]

/-- The event that the scaled equilibration time lies in a fixed finite window. -/
def scalingWindowEvent {Ω : Type*}
    (equilibrationTime : Nat → Real → Ω → ENNReal)
    (lower upper : Real) (N : Nat) (g : Real) : Set Ω :=
  scaledEquilibrationTime equilibrationTime N g ⁻¹'
    Icc (ENNReal.ofReal lower) (ENNReal.ofReal upper)

/-- Scaling-window events are measurable when the equilibration time is measurable. -/
theorem measurableSet_scalingWindowEvent {Ω : Type*} [MeasurableSpace Ω]
    (equilibrationTime : Nat → Real → Ω → ENNReal)
    (lower upper : Real) (N : Nat) (g : Real)
    (hT : Measurable (equilibrationTime N g)) :
    MeasurableSet (scalingWindowEvent equilibrationTime lower upper N g) := by
  exact measurableSet_Icc.preimage
    (measurable_scaledEquilibrationTime equilibrationTime N g hT)

/--
Constant-target convergence in probability, stated through measurable
neighbourhoods.  This formulation works directly for `ENNReal`, including its
top element, and avoids converting a potentially infinite random time to `Real`.
-/
def ConvergesInProbabilityTo {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (X : Nat → Ω → ENNReal) (a : ENNReal) : Prop :=
  (∀ j, Measurable (X j)) ∧
    ∀ U : Set ENNReal, MeasurableSet U → U ∈ 𝓝 a →
      Tendsto (fun j => ℙ (X j ⁻¹' U)) atTop (𝓝 1)

/-- Convergence in probability gives probability one asymptotically in every
closed interval whose endpoints strictly bracket the target. -/
theorem ConvergesInProbabilityTo.tendsto_measure_preimage_Icc
    {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ]
    {X : Nat → Ω → ENNReal} {a lower upper : ENNReal}
    (hX : ConvergesInProbabilityTo ℙ X a)
    (hlower : lower < a) (hupper : a < upper) :
    Tendsto (fun j => ℙ (X j ⁻¹' Icc lower upper)) atTop (𝓝 1) := by
  exact hX.2 (Icc lower upper) measurableSet_Icc
    (Icc_mem_nhds hlower hupper)

/-- A first, two-sided probabilistic `g⁻²` law along every admitted joint limit. -/
structure HighProbabilityG2Bounds {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (equilibrationTime : Nat → Real → Ω → ENNReal)
    (sizeCutoff : Real → Nat) (lower upper : Real) : Prop where
  /-- The lower kinetic-time bound is nontrivial. -/
  lower_pos : 0 < lower
  /-- The two constants form an ordered window. -/
  lower_le_upper : lower ≤ upper
  /-- The random hitting time is measurable for every finite model. -/
  equilibrationTime_measurable :
    ∀ N g, Measurable (equilibrationTime N g)
  /-- The probability of the kinetic-time window tends to one. -/
  law : ∀ s : AdmissibleJointLimit sizeCutoff,
    Tendsto (fun j => ℙ (scalingWindowEvent equilibrationTime lower upper
      (s.systemSize j) (s.coupling j))) atTop (𝓝 1)

/-- The enhanced target: `g² T_eq` converges in probability to a positive finite constant. -/
structure G2TeqConvergesInProbability {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (equilibrationTime : Nat → Real → Ω → ENNReal)
    (sizeCutoff : Real → Nat) (kineticTime : Real) : Prop where
  /-- The limiting kinetic hitting time is strictly positive. -/
  kineticTime_pos : 0 < kineticTime
  /-- The random hitting time is measurable for every finite model. -/
  equilibrationTime_measurable :
    ∀ N g, Measurable (equilibrationTime N g)
  /-- Every admitted joint limit has the same probabilistic kinetic-time limit. -/
  law : ∀ s : AdmissibleJointLimit sizeCutoff,
    ConvergesInProbabilityTo ℙ
      (fun j ω => scaledEquilibrationTime equilibrationTime
        (s.systemSize j) (s.coupling j) ω)
      (ENNReal.ofReal kineticTime)

/-- A positive finite probabilistic limit implies every strictly bracketing
high-probability two-sided bound. -/
theorem G2TeqConvergesInProbability.toHighProbabilityG2Bounds
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω)
    [IsProbabilityMeasure ℙ]
    (equilibrationTime : Nat → Real → Ω → ENNReal)
    (sizeCutoff : Real → Nat) (kineticTime lower upper : Real)
    (h : G2TeqConvergesInProbability ℙ equilibrationTime sizeCutoff kineticTime)
    (hlower_pos : 0 < lower) (hlower : lower < kineticTime)
    (hupper : kineticTime < upper) :
    HighProbabilityG2Bounds ℙ equilibrationTime sizeCutoff lower upper := by
  refine ⟨hlower_pos, hlower.le.trans hupper.le,
    h.equilibrationTime_measurable, ?_⟩
  intro s
  simpa only [scalingWindowEvent] using
    (h.law s).tendsto_measure_preimage_Icc
      ((ENNReal.ofReal_lt_ofReal_iff h.kineticTime_pos).2 hlower)
      ((ENNReal.ofReal_lt_ofReal_iff
        (h.kineticTime_pos.trans hupper)).2 hupper)

/-- The mean scaled time, as an extended integral that preserves infinite hitting times. -/
def meanScaledEquilibrationTime {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (equilibrationTime : Nat → Real → Ω → ENNReal)
    (N : Nat) (g : Real) : ENNReal :=
  ∫⁻ ω, scaledEquilibrationTime equilibrationTime N g ω ∂ℙ

/-- The stronger mean layer along every admitted joint limit.  This is only a
predicate; deriving it from convergence in probability requires a separate
uniform-integrability or tail hypothesis. -/
structure MeanG2TeqLimit {Ω : Type*} [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (equilibrationTime : Nat → Real → Ω → ENNReal)
    (sizeCutoff : Real → Nat) (kineticTime : Real) : Prop where
  /-- The limiting mean kinetic time is strictly positive. -/
  kineticTime_pos : 0 < kineticTime
  /-- The random hitting time is measurable for every finite model. -/
  equilibrationTime_measurable :
    ∀ N g, Measurable (equilibrationTime N g)
  /-- The scaled extended expectations converge to the stated finite value. -/
  law : ∀ s : AdmissibleJointLimit sizeCutoff,
    Tendsto (fun j => meanScaledEquilibrationTime ℙ equilibrationTime
      (s.systemSize j) (s.coupling j)) atTop
      (𝓝 (ENNReal.ofReal kineticTime))

end

end ArchonPhysics.ThermalizationTransfer
