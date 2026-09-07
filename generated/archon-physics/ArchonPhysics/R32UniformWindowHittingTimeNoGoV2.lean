import ArchonPhysics.CanonicalFrozenClosedHittingRescaling
import ArchonPhysics.ProbabilisticHittingTransfer
import ArchonPhysics.R32SupervolumeJointLimit

/-!
# Direct uniform-window no-go for the frozen hitting-time law (V2)

This module does not use a kinetic model or an F2/F3 certificate.  Its
scientific premise is genuinely uniform microscopic persistence: on every
fixed positive kinetic window, one high-probability event keeps the actual
scaled distance strictly above the hitting threshold at every positive time
in that window.

The order of quantifiers is essential.  Fixed-time persistence does not
exclude a narrow threshold hit at a time depending on the sample and the
system size.  `UniformWindowPersistence` instead places the time quantifier
inside the event whose probability tends to one.
-/

namespace ArchonPhysics.R32UniformWindowHittingTimeNoGoV2

open ArchonPhysics
open ArchonPhysics.CanonicalFrozenClosedHittingRescaling
open ArchonPhysics.ProbabilisticHittingTransfer
open ArchonPhysics.R32SupervolumeJointLimit
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

local instance canonicalProbabilityMeasure :
    IsProbabilityMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨canonicalIIDMassPhaseEnsemble.probability_univ⟩

/-- One event on which the microscopic distance stays above `delta + eta`
at every strictly positive kinetic time through `T`. -/
def uniformWindowLowerEvent
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta eta T : Real) {sizeCutoff : Real -> Nat}
    (s : AdmissibleJointLimit sizeCutoff) (j : Nat) :
    Set RandomEnsemble.SampleSpace :=
  {omega | forall tau : Real, 0 < tau -> tau <= T ->
    delta + eta <=
      scaledDistance kappa beta hbeta mu
        (s.systemSize j) (s.coupling j) omega tau}

/-- Uniform-in-window microscopic persistence along one admissible joint
limit.  The margin may depend on the requested finite window, but not on the
sample, the finite-volume index, or the time inside the window. -/
def UniformWindowPersistence
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (sizeCutoff : Real -> Nat)
    (s : AdmissibleJointLimit sizeCutoff) : Prop :=
  forall T : Real, 0 < T ->
    exists eta : Real, 0 < eta /\
      Tendsto
        (fun j => canonicalIIDMassPhaseEnsemble.probability
          (uniformWindowLowerEvent kappa beta hbeta mu delta eta T s j))
        atTop (nhds 1)

/-- The fixed numerical lower bound proposed in the R32 dilution route. -/
def oneSixteenthUniformWindowEvent
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu T : Real) {sizeCutoff : Real -> Nat}
    (s : AdmissibleJointLimit sizeCutoff) (j : Nat) :
    Set RandomEnsemble.SampleSpace :=
  {omega | forall tau : Real, 0 < tau -> tau <= T ->
    (1 : Real) / 16 <=
      scaledDistance kappa beta hbeta mu
        (s.systemSize j) (s.coupling j) omega tau}

/-- Probability-one persistence of the fixed `1 / 16` lower bound on every
finite positive kinetic window. -/
def OneSixteenthUniformWindowPersistence
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu : Real) (sizeCutoff : Real -> Nat)
    (s : AdmissibleJointLimit sizeCutoff) : Prop :=
  forall T : Real, 0 < T ->
    Tendsto
      (fun j => canonicalIIDMassPhaseEnsemble.probability
        (oneSixteenthUniformWindowEvent kappa beta hbeta mu T s j))
      atTop (nhds 1)

/-- A uniform `1 / 16` lower bound gives a positive threshold separation
exactly when the threshold is strictly below `1 / 16`. -/
theorem OneSixteenthUniformWindowPersistence.toUniformWindowPersistence
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} {sizeCutoff : Real -> Nat}
    {s : AdmissibleJointLimit sizeCutoff}
    (hpersistence : OneSixteenthUniformWindowPersistence
      kappa beta hbeta mu sizeCutoff s)
    (hdelta : delta < (1 : Real) / 16) :
    UniformWindowPersistence
      kappa beta hbeta mu delta sizeCutoff s := by
  intro T hT
  let eta : Real := ((1 : Real) / 16 - delta) / 2
  have heta : 0 < eta := by
    dsimp [eta]
    linarith
  refine ⟨eta, heta, ?_⟩
  apply tendsto_measure_superset_atTop_one
    canonicalIIDMassPhaseEnsemble.probability
    (fun j => oneSixteenthUniformWindowEvent
      kappa beta hbeta mu T s j)
    (fun j => uniformWindowLowerEvent
      kappa beta hbeta mu delta eta T s j)
    (hpersistence T hT)
  intro j omega homega
  change forall tau : Real, 0 < tau -> tau <= T ->
    (1 : Real) / 16 <=
      scaledDistance kappa beta hbeta mu
        (s.systemSize j) (s.coupling j) omega tau at homega
  change forall tau : Real, 0 < tau -> tau <= T ->
    delta + eta <=
      scaledDistance kappa beta hbeta mu
        (s.systemSize j) (s.coupling j) omega tau
  intro tau htau htauT
  have hseparation : delta + eta <= (1 : Real) / 16 := by
    dsimp [eta]
    linarith
  exact hseparation.trans (homega tau htau htauT)

/-- Uniform microscopic persistence along one admissible path directly rules
out every finite high-probability `g^2 T_eq` window for the actual canonical
measurable hitting time.

The hitting-time lower bound is derived from the uniform path event using
`coe_toNNReal_le_distanceThresholdHittingTime_of_no_hit_before`, then
transferred to the measurable equilibration time by the canonical a.e.
hitting-time identification. -/
theorem not_exists_highProbabilityG2Bounds_of_uniformWindowPersistence
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hdelta : delta < (1 : Real) / 8)
    {sizeCutoff : Real -> Nat}
    {s : AdmissibleJointLimit sizeCutoff}
    (hpersistence : UniformWindowPersistence
      kappa beta hbeta mu delta sizeCutoff s) :
    ¬ ∃ lower upper : Real,
      HighProbabilityG2Bounds
        canonicalIIDMassPhaseEnsemble.probability
        (measurableClosedEquilibrationTime
          kappa beta hbeta mu delta)
        sizeCutoff lower upper := by
  rintro ⟨lower, upper, bounds⟩
  let probability := canonicalIIDMassPhaseEnsemble.probability
  let T : Real := upper + 1
  have hupper_pos : 0 < upper :=
    bounds.lower_pos.trans_le bounds.lower_le_upper
  have hT : 0 < T := by
    dsimp [T]
    linarith
  have hupper_lt_T : upper < T := by
    dsimp [T]
    linarith
  obtain ⟨eta, heta, hgoodOne⟩ := hpersistence T hT
  let goodEvent : Nat -> Set RandomEnsemble.SampleSpace :=
    fun j => uniformWindowLowerEvent
      kappa beta hbeta mu delta eta T s j
  let successEvent : Nat -> Set RandomEnsemble.SampleSpace :=
    fun j => scalingWindowEvent
      (measurableClosedEquilibrationTime
        kappa beta hbeta mu delta)
      lower upper (s.systemSize j) (s.coupling j)
  have hgoodOne' :
      Tendsto (fun j => probability (goodEvent j)) atTop (nhds 1) := by
    simpa only [probability, goodEvent] using hgoodOne
  have hsuccessOne :
      Tendsto (fun j => probability (successEvent j)) atTop (nhds 1) := by
    simpa only [probability, successEvent] using bounds.law s
  have hsuccessMeasurable (j : Nat) :
      MeasurableSet (successEvent j) := by
    dsimp only [successEvent]
    exact measurableSet_scalingWindowEvent
      (measurableClosedEquilibrationTime
        kappa beta hbeta mu delta)
      lower upper (s.systemSize j) (s.coupling j)
      (bounds.equilibrationTime_measurable
        (s.systemSize j) (s.coupling j))
  have hgood_le_compl (j : Nat) :
      probability (goodEvent j) <= probability ((successEvent j)ᶜ) := by
    apply measure_mono_ae
    filter_upwards
      [scaled_measurableClosedEquilibrationTime_eq_hittingTime_ae
        kappa beta hbeta mu delta hmu0 hmu1 hdelta
        (s.systemSize j) (s.coupling j)
        (ne_of_gt (s.coupling_pos j))] with omega heq
    intro hgood
    change forall tau : Real, 0 < tau -> tau <= T ->
      delta + eta <=
        scaledDistance kappa beta hbeta mu
          (s.systemSize j) (s.coupling j) omega tau at hgood
    change omega ∉ successEvent j
    intro hsuccess
    have hnoHit : forall tau : Real, 0 < tau -> tau <= T ->
        delta <
          scaledDistance kappa beta hbeta mu
            (s.systemSize j) (s.coupling j) omega tau := by
      intro tau htau htauT
      have hlower := hgood tau htau htauT
      linarith
    have hrawLower :
        (Real.toNNReal T : ENNReal) <=
          distanceThresholdHittingTime
            (scaledDistance kappa beta hbeta mu
              (s.systemSize j) (s.coupling j) omega)
            delta :=
      coe_toNNReal_le_distanceThresholdHittingTime_of_no_hit_before
        hT.le hnoHit
    have hactualLower :
        (Real.toNNReal T : ENNReal) <=
          scaledEquilibrationTime
            (measurableClosedEquilibrationTime
              kappa beta hbeta mu delta)
            (s.systemSize j) (s.coupling j) omega := by
      rw [heq]
      exact hrawLower
    change
      scaledEquilibrationTime
          (measurableClosedEquilibrationTime
            kappa beta hbeta mu delta)
          (s.systemSize j) (s.coupling j) omega ∈
        Icc (ENNReal.ofReal lower) (ENNReal.ofReal upper) at hsuccess
    have hactualUpper :
        scaledEquilibrationTime
            (measurableClosedEquilibrationTime
              kappa beta hbeta mu delta)
            (s.systemSize j) (s.coupling j) omega <=
          (Real.toNNReal upper : ENNReal) := by
      simpa only [ENNReal.ofReal] using hsuccess.2
    have hstrictOfReal :
        ENNReal.ofReal upper < ENNReal.ofReal T :=
      (ENNReal.ofReal_lt_ofReal_iff hT).2 hupper_lt_T
    have hstrict :
        (Real.toNNReal upper : ENNReal) <
          (Real.toNNReal T : ENNReal) := by
      simpa only [ENNReal.ofReal] using hstrictOfReal
    exact (not_lt_of_ge (hactualLower.trans hactualUpper)) hstrict
  have hcomplOne :
      Tendsto (fun j => probability ((successEvent j)ᶜ))
        atTop (nhds 1) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      hgoodOne' tendsto_const_nhds hgood_le_compl (fun j => by
        calc
          probability ((successEvent j)ᶜ) <=
              probability (Set.univ : Set RandomEnsemble.SampleSpace) :=
            measure_mono (subset_univ _)
          _ = 1 := measure_univ)
  have hcomplZero :
      Tendsto (fun j => probability ((successEvent j)ᶜ))
        atTop (nhds 0) := by
    have hsub := ENNReal.Tendsto.sub
      (tendsto_const_nhds :
        Tendsto (fun _j : Nat => (1 : ENNReal)) atTop (nhds 1))
      hsuccessOne (Or.inl ENNReal.one_ne_top)
    have hmeasureCompl :
        (fun j => probability ((successEvent j)ᶜ)) =
          (fun j => 1 - probability (successEvent j)) := by
      funext j
      rw [measure_compl (hsuccessMeasurable j)
        (measure_ne_top probability (successEvent j)), measure_univ]
    rw [hmeasureCompl]
    simpa using hsub
  have hzero_eq_one : (0 : ENNReal) = 1 :=
    tendsto_nhds_unique hcomplZero hcomplOne
  exact zero_ne_one hzero_eq_one

/-- Specialization of the direct no-go to the explicit supervolume path. -/
theorem not_exists_highProbabilityG2Bounds_of_supervolumePersistence
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hdelta : delta < (1 : Real) / 8)
    (sizeCutoff : Real -> Nat)
    (hpersistence : UniformWindowPersistence
      kappa beta hbeta mu delta sizeCutoff
        (supervolumeJointLimit sizeCutoff)) :
    ¬ ∃ lower upper : Real,
      HighProbabilityG2Bounds
        canonicalIIDMassPhaseEnsemble.probability
        (measurableClosedEquilibrationTime
          kappa beta hbeta mu delta)
        sizeCutoff lower upper :=
  not_exists_highProbabilityG2Bounds_of_uniformWindowPersistence
    hmu0 hmu1 hdelta hpersistence

/-- If supervolume persistence is available for every proposed finite-size
cutoff, then no proof-produced cutoff and no pair of finite kinetic constants
can satisfy the unconditional high-probability hitting-time law. -/
theorem not_exists_cutoff_highProbabilityG2Bounds_of_uniformSupervolumePersistence
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hdelta : delta < (1 : Real) / 8)
    (hpersistence : forall sizeCutoff : Real -> Nat,
      UniformWindowPersistence
        kappa beta hbeta mu delta sizeCutoff
          (supervolumeJointLimit sizeCutoff)) :
    ¬ ∃ (sizeCutoff : Real -> Nat) (lower upper : Real),
      HighProbabilityG2Bounds
        canonicalIIDMassPhaseEnsemble.probability
        (measurableClosedEquilibrationTime
          kappa beta hbeta mu delta)
        sizeCutoff lower upper := by
  rintro ⟨sizeCutoff, lower, upper, bounds⟩
  exact
    (not_exists_highProbabilityG2Bounds_of_supervolumePersistence
      hmu0 hmu1 hdelta sizeCutoff (hpersistence sizeCutoff))
      ⟨lower, upper, bounds⟩

/-- Fixed-`1 / 16` version of the all-cutoff direct no-go.  The stricter
threshold hypothesis is necessary: `distance >= 1 / 16` does not exclude a
hit at a threshold `delta >= 1 / 16`. -/
theorem not_exists_cutoff_highProbabilityG2Bounds_of_oneSixteenthPersistence
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real} (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hdelta : delta < (1 : Real) / 16)
    (hpersistence : forall sizeCutoff : Real -> Nat,
      OneSixteenthUniformWindowPersistence
        kappa beta hbeta mu sizeCutoff
          (supervolumeJointLimit sizeCutoff)) :
    ¬ ∃ (sizeCutoff : Real -> Nat) (lower upper : Real),
      HighProbabilityG2Bounds
        canonicalIIDMassPhaseEnsemble.probability
        (measurableClosedEquilibrationTime
          kappa beta hbeta mu delta)
        sizeCutoff lower upper := by
  have hdelta_eighth : delta < (1 : Real) / 8 := by
    linarith
  apply not_exists_cutoff_highProbabilityG2Bounds_of_uniformSupervolumePersistence
    hmu0 hmu1 hdelta_eighth
  intro sizeCutoff
  exact (hpersistence sizeCutoff).toUniformWindowPersistence hdelta

end

end ArchonPhysics.R32UniformWindowHittingTimeNoGoV2

#print axioms ArchonPhysics.R32UniformWindowHittingTimeNoGoV2.not_exists_highProbabilityG2Bounds_of_uniformWindowPersistence
#print axioms ArchonPhysics.R32UniformWindowHittingTimeNoGoV2.not_exists_cutoff_highProbabilityG2Bounds_of_uniformSupervolumePersistence
#print axioms ArchonPhysics.R32UniformWindowHittingTimeNoGoV2.not_exists_cutoff_highProbabilityG2Bounds_of_oneSixteenthPersistence
