import ArchonPhysics.CanonicalReducedParametricGlobalFlow
import ArchonPhysics.RandomMassMeasurableHarmonicEnergy

/-!
# Global measurable physical modal observables for random-mass chains

A measurable flow on the common parameter--phase space can be sampled from
any measurable family of initial points.  This module reads its position and
canonical momentum coordinates and forms the genuine mass-weighted variables

`X = sqrt(M) q`, `Y = M^(-1/2) p`.

The resulting complete ordered harmonic-energy profile is jointly measurable
in the sample label and all real times.  A second profile is masked by
`positiveModeIndices`; it is therefore identically zero on every zero-frequency
mode, and its finite sum is exactly the sum over the strictly positive sector.

For a fixed mass realization in a common coercive energy shell, the canonical
cutoff flow is identified with the genuine untruncated reduced Hamiltonian
trajectory for all time.  The modal profile along that selected orbit is
therefore the physical profile of the true trajectory.  The canonical iid
specialization below establishes measurability for random initial data; it
does not by itself assert that every random initial datum lies in one common
reduced energy shell.  No kinetic or thermalization limit is asserted.
-/

open scoped Matrix

namespace ArchonPhysics.GlobalRandomMassModalObservable

open ArchonPhysics
open ArchonPhysics.CanonicalReducedParametricGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedHarmonicEnergy
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassOrderedProjectorBridge

noncomputable section

variable {S : Type*} [MeasurableSpace S]

/-- Position read from a common parameterized flow after selecting an initial
point by a sample label. -/
def sampledFlowPosition
    {N : Nat} [NeZero N]
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real) : HilbertConfiguration N :=
  (flow (initial st.1, st.2)).2.1

/-- Canonical momentum read from a common parameterized flow. -/
def sampledFlowMomentum
    {N : Nat} [NeZero N]
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real) : HilbertConfiguration N :=
  (flow (initial st.1, st.2)).2.2

theorem measurable_sampledFlowPosition
    {N : Nat} [NeZero N]
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hinitial : Measurable initial) (hflow : Measurable flow) :
    Measurable (sampledFlowPosition initial flow) := by
  exact (hflow.comp
    ((hinitial.comp measurable_fst).prodMk measurable_snd)).snd.fst

theorem measurable_sampledFlowMomentum
    {N : Nat} [NeZero N]
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hinitial : Measurable initial) (hflow : Measurable flow) :
    Measurable (sampledFlowMomentum initial flow) := by
  exact (hflow.comp
    ((hinitial.comp measurable_fst).prodMk measurable_snd)).snd.snd

/-- Physical energy of one ordered mode along a sampled flow.  The imported
observable performs the two mass-weighted transforms before applying the
basis-free ordered spectral projector. -/
def sampledPhysicalOrderedModeEnergyAlongFlow
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real)
    (k : Fin (Fintype.card (Lattice.Site N))) : Real :=
  harmonicOrderedPhysicalModeEnergy
    (fun st : S × Real ↦ massSample st.1)
    (sampledFlowPosition initial flow)
    (sampledFlowMomentum initial flow) st k

theorem measurable_sampledPhysicalOrderedModeEnergyAlongFlow
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    Measurable fun st ↦
      sampledPhysicalOrderedModeEnergyAlongFlow
        massSample initial flow st k := by
  exact measurable_harmonicOrderedPhysicalModeEnergy
    (fun st : S × Real ↦ massSample st.1)
    (sampledFlowPosition initial flow)
    (sampledFlowMomentum initial flow)
    (fun i ↦ (hmass i).comp measurable_fst)
    (measurable_sampledFlowPosition initial flow hinitial hflow)
    (measurable_sampledFlowMomentum initial flow hinitial hflow) k

omit [MeasurableSpace S] in
theorem sampledPhysicalOrderedModeEnergyAlongFlow_nonneg
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real) (k : Fin (Fintype.card (Lattice.Site N))) :
    0 ≤ sampledPhysicalOrderedModeEnergyAlongFlow
      massSample initial flow st k :=
  harmonicOrderedPhysicalModeEnergy_nonneg
    (fun st : S × Real ↦ massSample st.1)
    (sampledFlowPosition initial flow)
    (sampledFlowMomentum initial flow) st k

/-- The complete ordered physical energy vector at a sample--time point. -/
def sampledPhysicalOrderedEnergyProfileAlongFlow
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real) :
    Fin (Fintype.card (Lattice.Site N)) → Real :=
  fun k ↦ sampledPhysicalOrderedModeEnergyAlongFlow
    massSample initial flow st k

theorem measurable_sampledPhysicalOrderedEnergyProfileAlongFlow
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow) :
    Measurable (sampledPhysicalOrderedEnergyProfileAlongFlow
      massSample initial flow) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_sampledPhysicalOrderedModeEnergyAlongFlow
    massSample initial flow hmass hinitial hflow k

omit [MeasurableSpace S] in
/-- The complete profile has nonnegative entries at every sample and time. -/
theorem sampledPhysicalOrderedEnergyProfileAlongFlow_nonneg
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real) (k : Fin (Fintype.card (Lattice.Site N))) :
    0 ≤ sampledPhysicalOrderedEnergyProfileAlongFlow
      massSample initial flow st k :=
  sampledPhysicalOrderedModeEnergyAlongFlow_nonneg
    massSample initial flow st k

/-- Physical energy profile masked to the realization-dependent strictly
positive spectrum.  Every zero-frequency mode is explicitly assigned zero. -/
def sampledPositivePhysicalOrderedEnergyProfileAlongFlow
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real)
    (k : Fin (Fintype.card (Lattice.Site N))) : Real :=
  if k ∈ positiveModeIndices
      (harmonicHermitianSample massSample st.1) then
    sampledPhysicalOrderedModeEnergyAlongFlow massSample initial flow st k
  else 0

theorem measurable_sampledPositivePhysicalOrderedEnergyProfileAlongFlow_apply
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    Measurable fun st ↦
      sampledPositivePhysicalOrderedEnergyProfileAlongFlow
        massSample initial flow st k := by
  apply Measurable.ite
  · exact (measurableSet_mem_positiveModeIndices_unconditional
      (harmonicHermitianSample massSample)
      (measurable_harmonicHermitianSample massSample hmass) k).preimage
        measurable_fst
  · exact measurable_sampledPhysicalOrderedModeEnergyAlongFlow
      massSample initial flow hmass hinitial hflow k
  · exact measurable_const

theorem measurable_sampledPositivePhysicalOrderedEnergyProfileAlongFlow
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow) :
    Measurable (sampledPositivePhysicalOrderedEnergyProfileAlongFlow
      massSample initial flow) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_sampledPositivePhysicalOrderedEnergyProfileAlongFlow_apply
    massSample initial flow hmass hinitial hflow k

omit [MeasurableSpace S] in
theorem sampledPositivePhysicalOrderedEnergyProfileAlongFlow_nonneg
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real) (k : Fin (Fintype.card (Lattice.Site N))) :
    0 ≤ sampledPositivePhysicalOrderedEnergyProfileAlongFlow
      massSample initial flow st k := by
  by_cases hk : k ∈ positiveModeIndices
      (harmonicHermitianSample massSample st.1)
  · rw [sampledPositivePhysicalOrderedEnergyProfileAlongFlow, if_pos hk]
    exact sampledPhysicalOrderedModeEnergyAlongFlow_nonneg
      massSample initial flow st k
  · simp [sampledPositivePhysicalOrderedEnergyProfileAlongFlow, hk]

omit [MeasurableSpace S] in
theorem sampledPositivePhysicalOrderedEnergyProfileAlongFlow_eq_zero
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real) (k : Fin (Fintype.card (Lattice.Site N)))
    (hk : k ∉ positiveModeIndices
      (harmonicHermitianSample massSample st.1)) :
    sampledPositivePhysicalOrderedEnergyProfileAlongFlow
      massSample initial flow st k = 0 := by
  simp [sampledPositivePhysicalOrderedEnergyProfileAlongFlow, hk]

/-- Total physical harmonic energy over the strictly positive ordered modes. -/
def sampledPositivePhysicalEnergySumAlongFlow
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real) : Real :=
  ∑ k, sampledPositivePhysicalOrderedEnergyProfileAlongFlow
    massSample initial flow st k

omit [MeasurableSpace S] in
theorem sampledPositivePhysicalEnergySumAlongFlow_eq_finset
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real) :
    sampledPositivePhysicalEnergySumAlongFlow massSample initial flow st =
      ∑ k ∈ positiveModeIndices (harmonicHermitianSample massSample st.1),
        sampledPhysicalOrderedModeEnergyAlongFlow
          massSample initial flow st k := by
  classical
  unfold sampledPositivePhysicalEnergySumAlongFlow
    sampledPositivePhysicalOrderedEnergyProfileAlongFlow
    positiveModeIndices
  rw [Finset.sum_filter]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem measurable_sampledPositivePhysicalEnergySumAlongFlow
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow) :
    Measurable (sampledPositivePhysicalEnergySumAlongFlow
      massSample initial flow) := by
  unfold sampledPositivePhysicalEnergySumAlongFlow
  apply Finset.measurable_sum
  intro k _hk
  exact measurable_sampledPositivePhysicalOrderedEnergyProfileAlongFlow_apply
    massSample initial flow hmass hinitial hflow k

omit [MeasurableSpace S] in
theorem sampledPositivePhysicalEnergySumAlongFlow_nonneg
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real) :
    0 ≤ sampledPositivePhysicalEnergySumAlongFlow
      massSample initial flow st := by
  unfold sampledPositivePhysicalEnergySumAlongFlow
  exact Finset.sum_nonneg fun k _hk ↦
    sampledPositivePhysicalOrderedEnergyProfileAlongFlow_nonneg
      massSample initial flow st k

omit [MeasurableSpace S] in
/-- Every realization has at least one harmonic zero mode, and the positive
profile explicitly removes one such mode at every time. -/
theorem exists_zeroMode_excluded_from_sampledPositiveProfile
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real) :
    ∃ k : Fin (Fintype.card (Lattice.Site N)),
      harmonicOrderedEigenvalue massSample st.1 k = 0 ∧
      sampledPositivePhysicalOrderedEnergyProfileAlongFlow
        massSample initial flow st k = 0 := by
  obtain ⟨k, hk⟩ :=
    exists_harmonicOrderedEigenvalue_eq_zero massSample st.1
  refine ⟨k, hk, ?_⟩
  apply sampledPositivePhysicalOrderedEnergyProfileAlongFlow_eq_zero
  change orderedEigenvalue (harmonicHermitianSample massSample st.1) k = 0 at hk
  simp [positiveModeIndices, orderedModeFrequency, hk]

/-- Physical modal energy of one point in a mass-dependent reduced phase
space, written directly in `X = sqrt(M)q`, `Y = M^(-1/2)p` coordinates. -/
def reducedPhysicalOrderedModeEnergy
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (z : ReducedPhaseSpace m)
    (k : Fin (Fintype.card (Lattice.Site N))) : Real :=
  orderedHarmonicModeEnergy
    (harmonicHermitianSample (fun _ : Unit ↦ m) ()) k
    (sqrtMassTransform m (z.1 : HilbertConfiguration N))
    (inverseSqrtMassTransform m (z.2 : HilbertConfiguration N))

omit [MeasurableSpace S] in
/-- If a sampled ambient flow point is the embedding of a genuine reduced
point, then the sampled observable is exactly its physical modal energy. -/
theorem sampledPhysicalOrderedModeEnergyAlongFlow_eq_reduced_of_match
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g : Real) (z : ReducedPhaseSpace m)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (st : S × Real)
    (hmatch : flow (initial st.1, st.2) =
      embedReducedPoint m kappa beta g z)
    (k : Fin (Fintype.card (Lattice.Site N))) :
    sampledPhysicalOrderedModeEnergyAlongFlow
      (fun _ : S ↦ m) initial flow st k =
      reducedPhysicalOrderedModeEnergy m z k := by
  simp [sampledPhysicalOrderedModeEnergyAlongFlow,
    harmonicOrderedPhysicalModeEnergy, massWeightedPositionSample,
    massWeightedMomentumSample, sampledFlowPosition, sampledFlowMomentum,
    reducedPhysicalOrderedModeEnergy, harmonicHermitianSample, hmatch, embedReducedPoint]

/-- Fixed-realization global synthesis.  The jointly measurable ambient
profile agrees, along the selected compatible initial point, with the true
untruncated coercive reduced Hamiltonian trajectory for every real time. -/
theorem exists_canonical_global_flow_with_physical_modal_observable
    {N : Nat} [NeZero N]
    {C mLower mUpper uLower uUpper kappa beta g H : Real}
    (hC : 0 ≤ C)
    (hPoincare : ∀ (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) →
        ‖q‖ ≤ C * ‖Lattice.forwardDifference q‖)
    (hmLowerPos : 0 < mLower) (huLowerNonneg : 0 ≤ uLower)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (m : Lattice.PositiveMassConfig N)
    (hmLower : ∀ i, mLower ≤ m.mass i)
    (hmUpper : ∀ i, m.mass i ≤ mUpper)
    (huLower : ∀ i, uLower ≤ (m.mass i)⁻¹)
    (huUpper : ∀ i, (m.mass i)⁻¹ ≤ uUpper)
    (z0 : ReducedPhaseSpace m)
    (henergy0 : reducedHamiltonian m kappa beta g z0 ≤ H) :
    ∃ R : Real, 0 ≤ R ∧
      ∃ flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N,
        ∃ z : Real → ReducedPhaseSpace m,
          Measurable flow ∧ z 0 = z0 ∧
          (∀ t, flow (embedReducedPoint m kappa beta g z0, t) =
            embedReducedPoint m kappa beta g (z t)) ∧
          Measurable (sampledPhysicalOrderedEnergyProfileAlongFlow
            (fun _ : ParametricPhaseSpace N ↦ m) id flow) ∧
          Measurable (sampledPositivePhysicalOrderedEnergyProfileAlongFlow
            (fun _ : ParametricPhaseSpace N ↦ m) id flow) ∧
          Measurable (sampledPositivePhysicalEnergySumAlongFlow
            (fun _ : ParametricPhaseSpace N ↦ m) id flow) ∧
          (∀ t k, sampledPhysicalOrderedEnergyProfileAlongFlow
            (fun _ : ParametricPhaseSpace N ↦ m) id flow
              (embedReducedPoint m kappa beta g z0, t) k =
            reducedPhysicalOrderedModeEnergy m (z t) k) ∧
          (∀ x t k, 0 ≤ sampledPositivePhysicalOrderedEnergyProfileAlongFlow
            (fun _ : ParametricPhaseSpace N ↦ m) id flow (x, t) k) ∧
          (∀ t, ‖flow (embedReducedPoint m kappa beta g z0, t)‖ ≤ R) ∧
          ∀ t, HasDerivAt
            (fun s ↦ flow (embedReducedPoint m kappa beta g z0, s))
            (parameterizedHamiltonVectorField
              (flow (embedReducedPoint m kappa beta g z0, t))) t := by
  obtain ⟨R, hR, flow, hflow, _hzero, z, hz0, _hz,
      hmatch, hinside, hode, _henergy, _hjoint⟩ :=
    exists_canonical_measurable_global_flow_matching_reduced
      hC hPoincare hmLowerPos huLowerNonneg hbeta m
      hmLower hmUpper huLower huUpper z0 henergy0
  have hmass : ∀ i, Measurable fun _ : ParametricPhaseSpace N ↦ m.mass i :=
    fun _ ↦ measurable_const
  have hprofile :=
    measurable_sampledPhysicalOrderedEnergyProfileAlongFlow
      (fun _ : ParametricPhaseSpace N ↦ m) id flow hmass measurable_id hflow
  have hpositive :=
    measurable_sampledPositivePhysicalOrderedEnergyProfileAlongFlow
      (fun _ : ParametricPhaseSpace N ↦ m) id flow hmass measurable_id hflow
  have hsum :=
    measurable_sampledPositivePhysicalEnergySumAlongFlow
      (fun _ : ParametricPhaseSpace N ↦ m) id flow hmass measurable_id hflow
  refine ⟨R, hR, flow, z, hflow, hz0, hmatch,
    hprofile, hpositive, hsum, ?_, ?_, hinside, hode⟩
  · intro t k
    exact sampledPhysicalOrderedModeEnergyAlongFlow_eq_reduced_of_match
      m kappa beta g (z t) id flow
      (embedReducedPoint m kappa beta g z0, t) (hmatch t) k
  · intro x t k
    exact sampledPositivePhysicalOrderedEnergyProfileAlongFlow_nonneg
      (fun _ : ParametricPhaseSpace N ↦ m) id flow (x, t) k

/-- Canonical iid `[4/5,6/5]` random-mass specialization: for every measurable
random ambient initial point and every measurable ambient flow, the complete
physical ordered energy profile is jointly measurable in sample and time. -/
theorem canonical_measurable_sampledPhysicalOrderedEnergyProfileAlongFlow
    {N : Nat} [NeZero N]
    (initial : RandomEnsemble.SampleSpace → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hinitial : Measurable initial) (hflow : Measurable flow) :
    Measurable (sampledPhysicalOrderedEnergyProfileAlongFlow
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      initial flow) :=
  measurable_sampledPhysicalOrderedEnergyProfileAlongFlow
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    initial flow
    (measurable_restrictPositiveMass_coordinate
      canonicalIIDMassPhaseEnsemble) hinitial hflow

/-- The canonical iid strictly-positive-mode profile is jointly measurable. -/
theorem canonical_measurable_sampledPositivePhysicalOrderedEnergyProfileAlongFlow
    {N : Nat} [NeZero N]
    (initial : RandomEnsemble.SampleSpace → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hinitial : Measurable initial) (hflow : Measurable flow) :
    Measurable (sampledPositivePhysicalOrderedEnergyProfileAlongFlow
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      initial flow) :=
  measurable_sampledPositivePhysicalOrderedEnergyProfileAlongFlow
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    initial flow
    (measurable_restrictPositiveMass_coordinate
      canonicalIIDMassPhaseEnsemble) hinitial hflow

/-- The canonical iid total energy over all strictly positive modes is jointly
measurable in the sample and all real times. -/
theorem canonical_measurable_sampledPositivePhysicalEnergySumAlongFlow
    {N : Nat} [NeZero N]
    (initial : RandomEnsemble.SampleSpace → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hinitial : Measurable initial) (hflow : Measurable flow) :
    Measurable (sampledPositivePhysicalEnergySumAlongFlow
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      initial flow) :=
  measurable_sampledPositivePhysicalEnergySumAlongFlow
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    initial flow
    (measurable_restrictPositiveMass_coordinate
      canonicalIIDMassPhaseEnsemble) hinitial hflow

end

end ArchonPhysics.GlobalRandomMassModalObservable
