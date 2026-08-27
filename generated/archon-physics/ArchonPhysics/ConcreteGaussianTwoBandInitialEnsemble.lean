import ArchonPhysics.MassDependentHarmonicHaarPhasePropagation
import ArchonPhysics.OrderedPositiveInitialEnergyProfile

/-!
# A concrete Gaussian random-phase two-band initial ensemble

This module fixes one fully specified finite-volume initial ensemble:

* masses are iid `N(1, 1/100)` conditioned to the physical interval
  `[4/5, 6/5]`;
* phases are iid normalized Haar phases, independent of all masses;
* the positive ordered modes carry the quarter-contrast two-band profile;
* the translation mode carries zero energy; and
* at energy density `epsilon`, the total prescribed harmonic energy is
  `N * epsilon`.
The quarter-contrast two-band shape is a proof-friendly concrete default,
not the low-ten-percent excitation used in Figure 3 of arXiv:1903.09502;
this module does not claim pointwise identity with that numerical setup.

The corresponding wave action is `energy / frequency`, totalized to zero at
the translation mode.  We connect the concrete ensemble to the existing
mass-dependent free-harmonic Haar propagation theorem.

Here `Gaussian` refers only to the random masses.  Modal radii are fixed by
the deterministic energy profile: Haar phases alone do not provide a circular
complex-Gaussian amplitude law or Wick factorization.  A separate Rayleigh-
amplitude / complex-Gaussian RPA adapter is therefore an explicit next gap.

The remaining adapter is to reconstruct physical `q,p` in a measurable
Gaussian eigenframe; the existing full reconstruction is specialized to the
older uniform-mass ensemble, so it is intentionally not claimed here.

This is an exact initial-law and free-propagation result.  It does **not**
assert nonlinear random-phase propagation, a microscopic-to-kinetic limit,
or thermalization.
-/

namespace ArchonPhysics.ConcreteGaussianTwoBandInitialEnsemble

open MeasureTheory ProbabilityTheory
open ArchonPhysics
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.MassDependentHarmonicHaarPhasePropagation
open ArchonPhysics.MassDependentHarmonicHaarPhasePropagation.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.RandomPhaseMoments
open scoped BigOperators

noncomputable section

/-- Mean-one, variance-`1/100` Gaussian parameters before conditioning to the
positive compact mass interval. -/
def concreteMassParameters : TruncatedGaussianMassLaw.Parameters where
  mean := 1
  variance := 1 / 100
  variance_ne_zero := by norm_num

/-- Canonical product sample space carrying the independent mass and phase
blocks. -/
abbrev SampleSpace := TruncatedGaussianMassPhaseEnsemble.SampleSpace

/-- The concrete iid truncated-Gaussian mass / iid Haar-phase ensemble. -/
def concreteEnsemble :
    GaussianIIDMassPhaseEnsemble concreteMassParameters SampleSpace :=
  canonicalGaussianIIDMassPhaseEnsemble concreteMassParameters

/-- Ordered finite modes, with the final ordered index representing the
translation zero mode. -/
abbrev OrderedMode (N : Nat) [NeZero N] :=
  Fin (Fintype.card (Lattice.Site N))

/-- The fixed nonequilibrium shape: quarter-contrast two-band energy on the
positive ordered modes and zero energy on the translation mode. -/
def orderedEnergyShape (N : Nat) [NeZero N]
    (mode : OrderedMode N) : Real :=
  orderedPositiveInitialEnergyProfile
    (Fintype.card (Lattice.Site N)) (1 / 4) mode

/-- Prescribed ordered modal energy at energy density `epsilon`.  The factor
`N` makes its total energy extensive. -/
def orderedModalEnergy (N : Nat) [NeZero N] (energyDensity : Real)
    (mode : OrderedMode N) : Real :=
  (N : Real) * energyDensity * orderedEnergyShape N mode

/-- Attach the ordered energy profile to the finite phase coordinates using
the same reindexing as the measurable ordered-frequency advance. -/
def modalEnergyAtPhaseSite {N : Nat} [NeZero N]
    (energyDensity : Real) (mode : Lattice.Site N) : Real :=
  orderedModalEnergy N energyDensity (orderedModeIndexOfSite mode)

/-- The initial wave action `E / omega`.  Lean's totalized division makes the
zero-energy translation mode have action zero when its frequency is zero. -/
def initialAction {N : Nat} [NeZero N]
    (energyDensity : Real) (mass : MassSequence)
    (mode : Lattice.Site N) : Real :=
  modalEnergyAtPhaseSite energyDensity mode /
    massSequenceOrderedModeFrequency mass mode

/-- The concrete initial phase block. -/
def initialPhase {N : Nat} [NeZero N] (sample : SampleSpace) :
    Lattice.Site N -> UnitAddCircle :=
  concreteEnsemble.restrictPhase sample

/-- The concrete sample-dependent initial action block. -/
def initialActionSample {N : Nat} [NeZero N]
    (energyDensity : Real) (sample : SampleSpace) :
    Lattice.Site N -> Real :=
  initialAction energyDensity
    (ensembleMassSequence concreteEnsemble sample)

/-- The final ordered translation mode carries exactly zero shape energy. -/
@[simp] theorem orderedEnergyShape_translation_eq_zero
    {N : Nat} [NeZero N] :
    orderedEnergyShape N
      (lastSiteOrderedIndex (Fintype.card (Lattice.Site N))) = 0 := by
  exact orderedPositiveInitialEnergyProfile_last (a := (1 / 4 : Real))

/-- Hence the translation mode also carries zero extensive modal energy. -/
@[simp] theorem orderedModalEnergy_translation_eq_zero
    {N : Nat} [NeZero N] (energyDensity : Real) :
    orderedModalEnergy N energyDensity
      (lastSiteOrderedIndex (Fintype.card (Lattice.Site N))) = 0 := by
  simp [orderedModalEnergy]

/-- Every concrete mass coordinate has the requested conditioned Gaussian
law. -/
theorem massCoordinate_hasLaw (index : Nat) :
    HasLaw (concreteEnsemble.mass index)
      (TruncatedGaussianMassLaw.coordinateLaw concreteMassParameters)
      concreteEnsemble.probability :=
  concreteEnsemble.mass_hasLaw index

/-- Every concrete mass representative lies pointwise in `[4/5, 6/5]`. -/
theorem massCoordinate_mem_support (index : Nat) (sample : SampleSpace) :
    concreteEnsemble.mass index sample ∈ RandomEnsemble.massSupport :=
  concreteEnsemble.mass_mem_support index sample

/-- The deterministic ordered shape is nonnegative. -/
theorem orderedEnergyShape_nonneg {N : Nat} [NeZero N] (hN : 3 <= N)
    (mode : OrderedMode N) : 0 <= orderedEnergyShape N mode := by
  unfold orderedEnergyShape
  apply orderedPositiveInitialEnergyProfile_nonneg
  · simpa [Lattice.Site] using hN
  · norm_num
  · norm_num

/-- The deterministic ordered shape has total mass one. -/
theorem sum_orderedEnergyShape_eq_one {N : Nat} [NeZero N]
    (hN : 3 <= N) :
    (∑ mode : OrderedMode N, orderedEnergyShape N mode) = 1 := by
  unfold orderedEnergyShape
  apply sum_orderedPositiveInitialEnergyProfile_eq_one
  simpa [Lattice.Site] using hN

/-- At density `epsilon`, the prescribed total modal energy is exactly
`N * epsilon`. -/
theorem sum_orderedModalEnergy_eq_total {N : Nat} [NeZero N]
    (hN : 3 <= N)
    (energyDensity : Real) :
    (∑ mode : OrderedMode N, orderedModalEnergy N energyDensity mode) =
      (N : Real) * energyDensity := by
  simp only [orderedModalEnergy]
  rw [← Finset.mul_sum, sum_orderedEnergyShape_eq_one hN, mul_one]

/-- Nonnegative energy density gives nonnegative modal energies. -/
theorem orderedModalEnergy_nonneg {N : Nat} [NeZero N] (hN : 3 <= N)
    {energyDensity : Real} (henergyDensity : 0 <= energyDensity)
    (mode : OrderedMode N) :
    0 <= orderedModalEnergy N energyDensity mode := by
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg N) henergyDensity)
    (orderedEnergyShape_nonneg hN mode)

/-- The frozen shape is quantitatively separated from positive-mode
equipartition by the inherited `1/8` lower bound. -/
theorem orderedEnergyShape_l1_separated {N : Nat} [NeZero N]
    (hN : 3 <= N) :
    (1 / 8 : Real) <=
      ∑ mode : OrderedMode N,
        |orderedEnergyShape N mode -
          orderedPositiveUniformWeight
            (Fintype.card (Lattice.Site N)) mode| := by
  simpa [orderedEnergyShape, Lattice.Site] using
    (quarterAmplitude_orderedPositive_l1_lower
      (N := Fintype.card (Lattice.Site N))
      (by simpa [Lattice.Site] using hN))

/-- At every positive ordered frequency, multiplying the constructed action
by that frequency recovers the prescribed modal energy exactly. -/
theorem frequency_mul_initialAction {N : Nat} [NeZero N]
    (energyDensity : Real) (mass : MassSequence)
    (mode : Lattice.Site N)
    (hfrequency : 0 < massSequenceOrderedModeFrequency mass mode) :
    massSequenceOrderedModeFrequency mass mode *
        initialAction energyDensity mass mode =
      modalEnergyAtPhaseSite energyDensity mode := by
  unfold initialAction
  field_simp [hfrequency.ne']

/-- The initial action is nonnegative for nonnegative energy density. -/
theorem initialAction_nonneg {N : Nat} [NeZero N] (hN : 3 <= N)
    {energyDensity : Real} (henergyDensity : 0 <= energyDensity)
    (mass : MassSequence) (mode : Lattice.Site N) :
    0 <= initialAction energyDensity mass mode := by
  unfold initialAction modalEnergyAtPhaseSite
  exact div_nonneg
    (orderedModalEnergy_nonneg hN henergyDensity _)
    (Real.sqrt_nonneg _)

/-- The complete finite initial phase block has product Haar law. -/
theorem initialPhase_hasLaw {N : Nat} [NeZero N] :
    HasLaw (initialPhase (N := N))
      (finitePhaseHaarLaw (Lattice.Site N))
      concreteEnsemble.probability := by
  change HasLaw (concreteEnsemble.restrictPhase (N := N))
    (finitePhaseHaarLaw (Lattice.Site N)) concreteEnsemble.probability
  exact restrictPhase_hasLaw_finitePhaseHaarLaw concreteEnsemble

/-- The finite concrete mass block is independent of the complete initial
phase block. -/
theorem initialMass_indep_initialPhase {N : Nat} [NeZero N] :
    IndepFun (concreteEnsemble.restrictMass (N := N))
      (initialPhase (N := N)) concreteEnsemble.probability := by
  change IndepFun (concreteEnsemble.restrictMass (N := N))
    (concreteEnsemble.restrictPhase (N := N)) concreteEnsemble.probability
  exact concreteEnsemble.restrictMass_indep_restrictPhase

/-- Under the actual mass-dependent ordered free frequencies, the phase block
retains its complete product Haar law. -/
theorem freeEvolvedPhase_hasLaw {N : Nat} [NeZero N] (time : Real) :
    HasLaw
      (orderedMassDependentFreeRestrictedPhase
        (N := N) concreteEnsemble time)
      (finitePhaseHaarLaw (Lattice.Site N))
      concreteEnsemble.probability :=
  orderedMassDependentFreeRestrictedPhase_hasLaw concreteEnsemble time

/-- Under the same free evolution, the finite mass block remains independent
of the evolved phase block. -/
theorem initialMass_indep_freeEvolvedPhase {N : Nat} [NeZero N]
    (time : Real) :
    IndepFun (concreteEnsemble.restrictMass (N := N))
      (orderedMassDependentFreeRestrictedPhase
        (N := N) concreteEnsemble time)
      concreteEnsemble.probability :=
  restrictMass_indep_orderedMassDependentFreeRestrictedPhase
    concreteEnsemble time

end

end ArchonPhysics.ConcreteGaussianTwoBandInitialEnsemble
