import ArchonPhysics.PhyslibFPUTCouplingLawMomentControl

/-!
# Actual one-block Physlib bounded-Lipschitz amplitude law

The exact first-Duhamel estimate couples, phase by phase, the actual
interaction-picture amplitude at the end of one Physlib block with its
canonical Haar initial amplitude.  Taking the canonical phase torus itself as
the coupling probability space and the bad set to be empty gives a genuine
pushforward-law statement:

`d_BL,L(actual law, canonical initial law) <= L * epsilon_block`.

The corresponding second/fourth pushforward moments have errors
`2 M epsilon_block` and `4 M^3 epsilon_block`, and the canonical reference-law
moments are evaluated exactly.  This remains a single short-time block.  It
does not establish a conditional restart, propagation over many blocks, or a
kinetic-time result.
-/

namespace ArchonPhysics.PhyslibFPUTActualOneBlockBoundedLipschitzLaw

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.Lattice
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhyslibFPUTCouplingLawMomentControl
open ArchonPhysics.PhyslibFPUTRestartLawMomentPropagation
open ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/- Use exactly the normalized product Haar probability law from the one-block
RPA module. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance finitePhaseHaarLawIsProbability
    (d : Type*) [Fintype d] : IsProbabilityMeasure (finitePhaseHaarLaw d) := by
  unfold finitePhaseHaarLaw
  infer_instance

/-! ## The two amplitude pushforward laws -/

/-- End-of-block interaction-picture amplitude law of the actual Physlib
phase-indexed ensemble. -/
def actualPhyslibOneBlockAmplitudeLaw
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (observed : Site N)
    (p q : UnitAddTorus (Site N) → Time → HilbertConfiguration N)
    (T : Real) : Measure Complex :=
  Measure.map (actualInteractionPictureHaarAmplitude m observed p q T)
    (finitePhaseHaarLaw (Site N))

/-- Pushforward law of the canonical Haar initial amplitude. -/
def canonicalHaarInitialAmplitudeLaw
    {N : Nat} [NeZero N]
    (radius frequency : Site N → Real) (observed : Site N) :
    Measure Complex :=
  Measure.map
    (fun phase ↦ canonicalFreeComplexInitialAmplitude
      radius frequency phase observed)
    (finitePhaseHaarLaw (Site N))

/-! ## Exact reference-law moments -/

theorem integral_normSq_canonicalHaarInitialAmplitudeLaw
    {N : Nat} [NeZero N]
    (radius frequency : Site N → Real) (observed : Site N) :
    (∫ z, Complex.normSq z
      ∂canonicalHaarInitialAmplitudeLaw radius frequency observed) =
      canonicalHaarInitialMagnitude radius frequency observed ^ 2 := by
  rw [canonicalHaarInitialAmplitudeLaw,
    integral_map_of_stronglyMeasurable
      (measurable_canonicalFreeComplexInitialAmplitude
        radius frequency observed)
      Complex.continuous_normSq.measurable.stronglyMeasurable,
    integral_normSq_canonicalFreeComplexInitialAmplitude]

theorem integral_normSq_sq_canonicalHaarInitialAmplitudeLaw
    {N : Nat} [NeZero N]
    (radius frequency : Site N → Real) (observed : Site N) :
    (∫ z, Complex.normSq z ^ 2
      ∂canonicalHaarInitialAmplitudeLaw radius frequency observed) =
      canonicalHaarInitialMagnitude radius frequency observed ^ 4 := by
  rw [canonicalHaarInitialAmplitudeLaw,
    integral_map_of_stronglyMeasurable
      (measurable_canonicalFreeComplexInitialAmplitude
        radius frequency observed)
      (Complex.continuous_normSq.measurable.pow_const 2).stronglyMeasurable,
    integral_normSq_sq_canonicalFreeComplexInitialAmplitude]

/-! ## Actual one-block law endpoint -/

/-- The actual one-block amplitude law is close to its canonical Haar initial
law for every bounded real test with Lipschitz constant `L`.  The bad-event
probability is exactly zero because the first-Duhamel bound is pointwise in
the phase. -/
theorem actual_physlib_oneBlock_boundedLipschitz_law
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T L : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Site N)
    (p q : UnitAddTorus (Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ phase time, time ∈ Set.Icc 0 T →
      ∑ i, m.mass i *
        asConfiguration ((realReparametrize (q phase)) time) i = 0)
    (henergy : ∀ phase time, time ∈ Set.Icc 0 T →
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) time))
        (asConfiguration ((realReparametrize (q phase)) time)) ≤ H)
    (radius : Site N → Real)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (hactualMeasurable : Measurable
      (fun phase : UnitAddTorus (Site N) ↦
        physlibModeAmplitude m observed (p phase) (q phase) T))
    (hL : 0 ≤ L) :
    BoundedLipschitzTestLawDistanceAtMost
      (actualPhyslibOneBlockAmplitudeLaw m observed p q T)
      (canonicalHaarInitialAmplitudeLaw radius (modeFrequency m) observed)
      L (L * shortTimeRPABlockError
        m mUpper kappa beta g H observed T) := by
  let actual := actualInteractionPictureHaarAmplitude m observed p q T
  let initial := fun phase : UnitAddTorus (Site N) ↦
    canonicalFreeComplexInitialAmplitude
      radius (modeFrequency m) phase observed
  let epsilon := shortTimeRPABlockError
    m mUpper kappa beta g H observed T
  have hactual : Measurable actual :=
    measurable_actualInteractionPictureHaarAmplitude
      m observed p q T hactualMeasurable
  have hinitialMeasurable : Measurable initial :=
    measurable_canonicalFreeComplexInitialAmplitude
      radius (modeFrequency m) observed
  have hdistance : ∀ phase, ‖actual phase - initial phase‖ ≤ epsilon :=
    norm_actualInteractionPictureHaarAmplitude_sub_initial_le
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton homega hT
        hgauge henergy radius hinitial
  have hepsilon : 0 ≤ epsilon :=
    (norm_nonneg (actual 0 - initial 0)).trans (hdistance 0)
  have hlaw := boundedLipschitzTestLawDistanceAtMost_map_of_coupling
    (finitePhaseHaarLaw (Site N)) actual initial hactual hinitialMeasurable
      (∅ : Set (UnitAddTorus (Site N))) MeasurableSet.empty
      (p := 0) hepsilon hL (by simp)
      (fun phase _ ↦ by simpa [dist_eq_norm] using hdistance phase)
  simpa [actualPhyslibOneBlockAmplitudeLaw,
    canonicalHaarInitialAmplitudeLaw, actual, initial, epsilon] using hlaw

/-- Law-level second/fourth moment endpoint obtained from the same pointwise
coupling. -/
theorem actual_physlib_oneBlock_pushforward_moment_errors
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T M : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Site N)
    (p q : UnitAddTorus (Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ phase time, time ∈ Set.Icc 0 T →
      ∑ i, m.mass i *
        asConfiguration ((realReparametrize (q phase)) time) i = 0)
    (henergy : ∀ phase time, time ∈ Set.Icc 0 T →
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) time))
        (asConfiguration ((realReparametrize (q phase)) time)) ≤ H)
    (radius : Site N → Real)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (hactualMeasurable : Measurable
      (fun phase : UnitAddTorus (Site N) ↦
        physlibModeAmplitude m observed (p phase) (q phase) T))
    (hM : 0 ≤ M)
    (hactualBound : ∀ phase,
      ‖actualInteractionPictureHaarAmplitude m observed p q T phase‖ ≤ M)
    (hinitialBound : canonicalHaarInitialMagnitude
      radius (modeFrequency m) observed ≤ M) :
    |∫ z, Complex.normSq z
          ∂actualPhyslibOneBlockAmplitudeLaw m observed p q T -
        ∫ z, Complex.normSq z
          ∂canonicalHaarInitialAmplitudeLaw
            radius (modeFrequency m) observed| ≤
      2 * M * shortTimeRPABlockError
        m mUpper kappa beta g H observed T ∧
    |∫ z, Complex.normSq z ^ 2
          ∂actualPhyslibOneBlockAmplitudeLaw m observed p q T -
        ∫ z, Complex.normSq z ^ 2
          ∂canonicalHaarInitialAmplitudeLaw
            radius (modeFrequency m) observed| ≤
      4 * M ^ 3 * shortTimeRPABlockError
        m mUpper kappa beta g H observed T := by
  let actual := actualInteractionPictureHaarAmplitude m observed p q T
  let initial := fun phase : UnitAddTorus (Site N) ↦
    canonicalFreeComplexInitialAmplitude
      radius (modeFrequency m) phase observed
  let epsilon := shortTimeRPABlockError
    m mUpper kappa beta g H observed T
  have hactual : Measurable actual :=
    measurable_actualInteractionPictureHaarAmplitude
      m observed p q T hactualMeasurable
  have hinitialMeasurable : Measurable initial :=
    measurable_canonicalFreeComplexInitialAmplitude
      radius (modeFrequency m) observed
  have hdistance : ∀ phase, ‖actual phase - initial phase‖ ≤ epsilon :=
    norm_actualInteractionPictureHaarAmplitude_sub_initial_le
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton homega hT
        hgauge henergy radius hinitial
  have hepsilon : 0 ≤ epsilon :=
    (norm_nonneg (actual 0 - initial 0)).trans (hdistance 0)
  have hinitialPointwise : ∀ phase, ‖initial phase‖ ≤ M := by
    intro phase
    change ‖canonicalFreeComplexInitialAmplitude
      radius (modeFrequency m) phase observed‖ ≤ M
    rw [norm_canonicalFreeComplexInitialAmplitude]
    exact hinitialBound
  have hmoments := pushforward_second_fourth_moment_errors
    (finitePhaseHaarLaw (Site N)) actual initial hactual hinitialMeasurable
      (∅ : Set (UnitAddTorus (Site N))) MeasurableSet.empty
      (p := 0) hepsilon hM (by simp) (fun phase _ ↦ hdistance phase)
      hactualBound hinitialPointwise
  simpa [actualPhyslibOneBlockAmplitudeLaw,
    canonicalHaarInitialAmplitudeLaw, actual, initial, epsilon] using hmoments

/-- The law-level moments compared directly with the exact canonical Haar
values. -/
theorem actual_physlib_oneBlock_law_moments_to_canonical_values
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T M : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Site N)
    (p q : UnitAddTorus (Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ phase time, time ∈ Set.Icc 0 T →
      ∑ i, m.mass i *
        asConfiguration ((realReparametrize (q phase)) time) i = 0)
    (henergy : ∀ phase time, time ∈ Set.Icc 0 T →
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) time))
        (asConfiguration ((realReparametrize (q phase)) time)) ≤ H)
    (radius : Site N → Real)
    (hinitial : ∀ phase,
      physlibModeAmplitude m observed (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase observed)
    (hactualMeasurable : Measurable
      (fun phase : UnitAddTorus (Site N) ↦
        physlibModeAmplitude m observed (p phase) (q phase) T))
    (hM : 0 ≤ M)
    (hactualBound : ∀ phase,
      ‖actualInteractionPictureHaarAmplitude m observed p q T phase‖ ≤ M)
    (hinitialBound : canonicalHaarInitialMagnitude
      radius (modeFrequency m) observed ≤ M) :
    |∫ z, Complex.normSq z
          ∂actualPhyslibOneBlockAmplitudeLaw m observed p q T -
        canonicalHaarInitialMagnitude radius (modeFrequency m) observed ^ 2| ≤
      2 * M * shortTimeRPABlockError
        m mUpper kappa beta g H observed T ∧
    |∫ z, Complex.normSq z ^ 2
          ∂actualPhyslibOneBlockAmplitudeLaw m observed p q T -
        canonicalHaarInitialMagnitude radius (modeFrequency m) observed ^ 4| ≤
      4 * M ^ 3 * shortTimeRPABlockError
        m mUpper kappa beta g H observed T := by
  have hmoments := actual_physlib_oneBlock_pushforward_moment_errors
    m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton homega hT
      hgauge henergy radius hinitial hactualMeasurable hM hactualBound
        hinitialBound
  rw [integral_normSq_canonicalHaarInitialAmplitudeLaw,
    integral_normSq_sq_canonicalHaarInitialAmplitudeLaw] at hmoments
  exact hmoments

end

end ArchonPhysics.PhyslibFPUTActualOneBlockBoundedLipschitzLaw
