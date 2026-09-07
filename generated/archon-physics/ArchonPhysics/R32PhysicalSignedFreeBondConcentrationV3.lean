import ArchonPhysics.R32PhysicalSignedFreeBondEventsV3Final

/-!
# Annealed concentration for the physical-sign V3 free-bond event

This module completes the finite-grid probability half of the physical-sign
free-bond construction.  Conditional on the masses, every bond at every grid
time is a centered finite Haar sum whose coefficient-square mass is at most
`6 / (N - 1)`.  A finite union bound gives the explicit budget

`2 * N * freeTimeGridCard T g * exp (-N * g^8 / 96)`.

The product-law transfer is made through the globally measurable signed
ordered eigenframe.  It uses only the time-zero product Haar law and does not
assume independence of positive-time fields.
-/

namespace ArchonPhysics.R32PhysicalSignedFreeBondConcentrationV3

open ArchonPhysics
open ArchonPhysics.FiniteProductBoundedDifferences
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final
open ArchonPhysics.R32CanonicalProductTailTransferV2
open ArchonPhysics.R32HaarScalarTailCleanV4
open ArchonPhysics.R32PhysicalSignedFreeBondEventsV3Final
open ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final
open ArchonPhysics.R32SupervolumeConcentrationAsymptotic
open ArchonPhysics.R32SupervolumeJointLimit
open ArchonPhysics.RandomPhaseMoments
open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance finitePhaseHaarLawIsProbability
    (d : Type*) [Fintype d] : IsProbabilityMeasure (finitePhaseHaarLaw d) := by
  unfold finitePhaseHaarLaw
  infer_instance

local instance canonicalProbabilityMeasure :
    IsProbabilityMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨canonicalIIDMassPhaseEnsemble.probability_univ⟩

/-! ## Quenched fixed-time and grid tails -/

/-- Insert a deterministic upper bound for the exact coefficient-square
proxy in the clean fixed-time Haar tail. -/
theorem measureReal_abs_fixedTimeHaarScalarSum_gt_le_of_sum_sq_le
    {n : Nat} (coefficient frequency : Fin n → Real) (time : Real)
    {variance u : Real}
    (hvariance : 0 ≤ variance)
    (hsum : (∑ k, coefficient k ^ 2) ≤ variance)
    (hu : 0 ≤ u) :
    (finitePhaseHaarLaw (Fin n)).real
        {phase |
          |fixedTimeHaarScalarSum coefficient frequency time phase| > u} ≤
      2 * Real.exp (-u ^ 2 / (2 * variance)) := by
  let proxy : NNReal := ⟨variance, hvariance⟩
  have hproxy : haarScalarVarianceProxy coefficient ≤ proxy := by
    apply NNReal.coe_le_coe.mp
    change (∑ k, coefficient k ^ 2) ≤ variance
    exact hsum
  have hmgf : HasSubgaussianMGF
      (fixedTimeHaarScalarSum coefficient frequency time) proxy
      (finitePhaseHaarLaw (Fin n)) :=
    hasSubgaussianMGF_mono_parameter
      (hasSubgaussianMGF_fixedTimeHaarScalarSum
        coefficient frequency time) hproxy
  have htail := measureReal_abs_gt_le_of_hasSubgaussianMGF hmgf hu
  have hproxyReal : (proxy : Real) = variance := rfl
  rw [hproxyReal] at htail
  exact htail

/-- A physical-sign bond at one time has the inverse-volume Haar tail. -/
theorem physicalSignedHaarBondField_fixedTime_tail
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (bond : Lattice.Site N) (time : Real) {u : Real} (hu : 0 ≤ u) :
    (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
        {phase | |physicalSignedHaarBondField m bond phase time| > u} ≤
      2 * Real.exp
        (-u ^ 2 / (2 * (6 / (((N - 1 : Nat) : Real))))) := by
  unfold physicalSignedHaarBondField
  exact measureReal_abs_fixedTimeHaarScalarSum_gt_le_of_sum_sq_le
    (signedFrozenBondCoefficient m bond)
    (orderedModeFrequency (harmonicHermitian m)) (-time)
    (by positivity)
    (sum_sq_signedFrozenBondCoefficient_le_six_div_pred
      hN m hsimple bond) hu

/-- At threshold `g^4 / 2`, one bond and one physical time cost at most
`2 * exp (-N * g^8 / 96)`. -/
theorem physicalSignedHaarBondField_halfThreshold_tail
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (bond : Lattice.Site N) (time g : Real) :
    (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
        {phase |
          |physicalSignedHaarBondField m bond phase time| > g ^ 4 / 2} ≤
      2 * Real.exp (-(N : Real) * g ^ 8 / 96) := by
  have htail := physicalSignedHaarBondField_fixedTime_tail
    hN m hsimple bond time (u := g ^ 4 / 2) (by positivity)
  have hpredNat : 0 < N - 1 := by omega
  have hpred : 0 < (((N - 1 : Nat) : Real)) := by
    exact_mod_cast hpredNat
  have hNpredNat : N ≤ 2 * (N - 1) := by omega
  have hNpred : (N : Real) ≤ 2 * (((N - 1 : Nat) : Real)) := by
    exact_mod_cast hNpredNat
  have hexponent :
      -(g ^ 4 / 2) ^ 2 /
          (2 * (6 / (((N - 1 : Nat) : Real)))) =
        -(((N - 1 : Nat) : Real)) * g ^ 8 / 48 := by
    field_simp [ne_of_gt hpred]
    ring
  have harg :
      -(((N - 1 : Nat) : Real)) * g ^ 8 / 48 ≤
        -(N : Real) * g ^ 8 / 96 := by
    have hg8 : 0 ≤ g ^ 8 := by positivity
    nlinarith
  rw [hexponent] at htail
  calc
    (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
        {phase |
          |physicalSignedHaarBondField m bond phase time| > g ^ 4 / 2} ≤
        2 * Real.exp
          (-(((N - 1 : Nat) : Real)) * g ^ 8 / 48) := htail
    _ ≤ 2 * Real.exp (-(N : Real) * g ^ 8 / 96) := by
      gcongr

/-- The quenched physical-sign bad event on all bonds and grid times. -/
def physicalSignedFreeGridBadAtMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (T g : Real) :
    Set (HarmonicOrderedModeIndex N → UnitAddCircle) :=
  ⋃ index : Lattice.Site N × Fin (freeTimeGridCard T g),
    {phase |
      |physicalSignedHaarBondField m index.1 phase
        (freeTimeGrid T g index.2)| > g ^ 4 / 2}

theorem measurableSet_physicalSignedFreeGridBadAtMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (T g : Real) :
    MeasurableSet (physicalSignedFreeGridBadAtMass m T g) := by
  unfold physicalSignedFreeGridBadAtMass
  apply MeasurableSet.iUnion
  intro index
  change MeasurableSet {phase |
    g ^ 4 / 2 < |signedHaarBondField m index.1 phase
      (-(freeTimeGrid T g index.2))|}
  exact measurableSet_lt measurable_const
    (measurable_fixedTimeHaarScalarSum
      (signedFrozenBondCoefficient m index.1)
      (orderedModeFrequency (harmonicHermitian m))
      (-(freeTimeGrid T g index.2))).abs

/-- Quenched union bound over every physical bond and every grid time. -/
theorem physicalSignedFreeGridBadAtMass_measureReal_le
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (T g : Real) :
    (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
        (physicalSignedFreeGridBadAtMass m T g) ≤
      freeGridBadBudget T g N := by
  unfold physicalSignedFreeGridBadAtMass
  calc
    (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
        (⋃ index : Lattice.Site N × Fin (freeTimeGridCard T g),
          {phase |
            |physicalSignedHaarBondField m index.1 phase
              (freeTimeGrid T g index.2)| > g ^ 4 / 2}) ≤
        ∑ index : Lattice.Site N × Fin (freeTimeGridCard T g),
          (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
            {phase |
              |physicalSignedHaarBondField m index.1 phase
                (freeTimeGrid T g index.2)| > g ^ 4 / 2} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _index : Lattice.Site N × Fin (freeTimeGridCard T g),
        2 * Real.exp (-(N : Real) * g ^ 8 / 96) := by
      exact Finset.sum_le_sum fun index _ ↦
        physicalSignedHaarBondField_halfThreshold_tail
          hN m hsimple index.1 (freeTimeGrid T g index.2) g
    _ = freeGridBadBudget T g N := by
      simp [freeGridBadBudget, Fintype.card_prod]
      ring

/-! ## Canonical product-law transfer -/

/-- At a frozen simple mass, the canonical phase section is exactly the
pullback of the quenched physical-sign event. -/
theorem phaseSection_canonicalPhysicalSignedSimpleFreeGridBad_eq
    {N : Nat} [NeZero N]
    (T g : Real) (mass : RandomEnsemble.RawMassSequence)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (rawCanonicalFrozenMass (N := N) mass))) :
    Prod.mk mass ⁻¹'
        canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g =
      orderedPhaseBlockFromSequence (N := N) ⁻¹'
        physicalSignedFreeGridBadAtMass
          (rawCanonicalFrozenMass (N := N) mass) T g := by
  ext phase
  simp [canonicalPhysicalSignedSimpleFreeGridBad,
    physicalSignedFreeGridBadAtMass, hsimple]

/-- Every raw-mass phase section obeys the same budget; nonsimple sections
are empty by construction. -/
theorem phaseSection_canonicalPhysicalSignedSimpleFreeGridBad_measureReal_le
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (T g : Real) (mass : RandomEnsemble.RawMassSequence) :
    RandomEnsemble.phaseSequenceLaw.real
        (Prod.mk mass ⁻¹'
          canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g) ≤
      freeGridBadBudget T g N := by
  by_cases hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (rawCanonicalFrozenMass (N := N) mass))
  · rw [phaseSection_canonicalPhysicalSignedSimpleFreeGridBad_eq
      T g mass hsimple]
    have hmeasureReal :=
      (orderedPhaseBlockFromSequence_hasLaw (N := N)).measureReal_eq
        (measurableSet_physicalSignedFreeGridBadAtMass
          (rawCanonicalFrozenMass (N := N) mass) T g)
    change
      RandomEnsemble.phaseSequenceLaw.real
          (orderedPhaseBlockFromSequence (N := N) ⁻¹'
            physicalSignedFreeGridBadAtMass
              (rawCanonicalFrozenMass (N := N) mass) T g) =
        (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
          (physicalSignedFreeGridBadAtMass
            (rawCanonicalFrozenMass (N := N) mass) T g) at hmeasureReal
    calc
      RandomEnsemble.phaseSequenceLaw.real
          (orderedPhaseBlockFromSequence (N := N) ⁻¹'
            physicalSignedFreeGridBadAtMass
              (rawCanonicalFrozenMass (N := N) mass) T g) =
          (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
            (physicalSignedFreeGridBadAtMass
              (rawCanonicalFrozenMass (N := N) mass) T g) := hmeasureReal
      _ ≤ freeGridBadBudget T g N :=
        physicalSignedFreeGridBadAtMass_measureReal_le hN
          (rawCanonicalFrozenMass (N := N) mass) hsimple T g
  · have hevent :
        Prod.mk mass ⁻¹'
          canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g = ∅ := by
      ext phase
      simp [canonicalPhysicalSignedSimpleFreeGridBad, hsimple]
    rw [hevent]
    simp [freeGridBadBudget]
    positivity

/-- Annealed canonical physical-sign finite-grid tail. -/
theorem canonicalPhysicalSignedSimpleFreeGridBad_measureReal_le
    {N : Nat} [NeZero N] (hN : 3 ≤ N) (T g : Real) :
    canonicalIIDMassPhaseEnsemble.probability.real
        (canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g) ≤
      freeGridBadBudget T g N := by
  exact canonical_measureReal_le_of_phase_sections
    (canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g)
    (measurableSet_canonicalPhysicalSignedSimpleFreeGridBad T g)
    (phaseSection_canonicalPhysicalSignedSimpleFreeGridBad_measureReal_le
      hN T g)

/-! ## Probability of the physical-sign grid-good event -/

/-- The raw mass sequence used by the measurable signed field is the same
positive mass configuration as the canonical ensemble restriction. -/
theorem rawCanonicalFrozenMass_eq_restrictPositiveMass
    {N : Nat} [NeZero N] (sample : RandomEnsemble.SampleSpace) :
    rawCanonicalFrozenMass (N := N) sample.1 =
      canonicalIIDMassPhaseEnsemble.restrictPositiveMass sample := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  rfl

/-- The simple-spectrum guard in the physical-sign good event costs zero
canonical probability. -/
theorem rawCanonicalFrozenMass_simpleOrderedSpectrum_ae
    {N : Nat} [NeZero N] (hN : 3 ≤ N) :
    ∀ᵐ sample ∂canonicalIIDMassPhaseEnsemble.probability,
      SimpleOrderedSpectrum
        (harmonicHermitian (rawCanonicalFrozenMass (N := N) sample.1)) := by
  filter_upwards
    [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      canonicalIIDMassPhaseEnsemble (show 2 ≤ N by omega)] with sample hsimple
  rwa [rawCanonicalFrozenMass_eq_restrictPositiveMass]

/-- The complement of the Borel physical-sign grid-good event is bounded by
the same explicit annealed union budget. -/
theorem canonicalPhysicalSignedFreeGridGood_compl_measureReal_le
    {N : Nat} [NeZero N] (hN : 3 ≤ N) (T g : Real) :
    canonicalIIDMassPhaseEnsemble.probability.real
        ((canonicalPhysicalSignedFreeGridGood (N := N) T g)ᶜ) ≤
      freeGridBadBudget T g N := by
  have hae : ∀ᵐ sample ∂canonicalIIDMassPhaseEnsemble.probability,
      sample ∈ (canonicalPhysicalSignedFreeGridGood (N := N) T g)ᶜ →
        sample ∈ canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g := by
    filter_upwards [rawCanonicalFrozenMass_simpleOrderedSpectrum_ae hN]
      with sample hsimple
    intro hnotGood
    by_contra hnotBad
    exact hnotGood ⟨hsimple, hnotBad⟩
  have hmeasure :
      canonicalIIDMassPhaseEnsemble.probability
          ((canonicalPhysicalSignedFreeGridGood (N := N) T g)ᶜ) ≤
        canonicalIIDMassPhaseEnsemble.probability
          (canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g) :=
    measure_mono_ae hae
  calc
    canonicalIIDMassPhaseEnsemble.probability.real
        ((canonicalPhysicalSignedFreeGridGood (N := N) T g)ᶜ) ≤
        canonicalIIDMassPhaseEnsemble.probability.real
          (canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g) := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono
        (measure_ne_top canonicalIIDMassPhaseEnsemble.probability _) hmeasure
    _ ≤ freeGridBadBudget T g N :=
      canonicalPhysicalSignedSimpleFreeGridBad_measureReal_le hN T g

/-! ## Supervolume concentration -/

/-- The physical grid has `O(T g⁻⁶ + 1)` points. -/
theorem freeTimeGrid_card_le_polynomial_clean
    (T g : Real) (hT : 0 ≤ T) (hg : 0 < g) :
    (freeTimeGridCard T g : Real) ≤
      2 * (65536 * T * g⁻¹ ^ 6 + 1) := by
  have hscale : 0 < freeTimeGridScale := by
    norm_num [freeTimeGridScale]
  have hcard := kineticTimeGrid_card_le_polynomial
    (T / freeTimeGridScale ^ 2)
    (g / freeTimeGridScale)
    (div_nonneg hT (sq_nonneg freeTimeGridScale))
    (div_pos hg hscale)
  have hcard' : (freeTimeGridCard T g : Real) ≤
      2 * ((T / freeTimeGridScale ^ 2) *
        (g / freeTimeGridScale)⁻¹ ^ 6 + 1) := by
    simpa [freeTimeGridCard] using hcard
  calc
    (freeTimeGridCard T g : Real) ≤
        2 * ((T / freeTimeGridScale ^ 2) *
          (g / freeTimeGridScale)⁻¹ ^ 6 + 1) := hcard'
    _ = 2 * (65536 * T * g⁻¹ ^ 6 + 1) := by
      norm_num [freeTimeGridScale]
      field_simp [ne_of_gt hg]
      ring

/-- Pointwise comparison of the explicit grid budget with the already
proved arbitrary-supervolume exponential cost. -/
theorem freeGridBadBudget_le_concentrationUnionCost_clean
    (T : Real) (hT : 0 ≤ T) (N : Nat → Nat) (j : Nat) :
    freeGridBadBudget T (inverseLinearCoupling j) (N j) ≤
      4 * (65536 * T + 1) * concentrationUnionCost (1 / 96) N j := by
  let g := inverseLinearCoupling j
  have hg : 0 < g := inverseLinearCoupling_pos j
  have hgOne : g ≤ 1 := by
    dsimp [g, inverseLinearCoupling]
    have hj : (0 : Real) ≤ (j : Real) := by positivity
    exact (div_le_one (by positivity)).2 (by linarith)
  have hinv : 1 ≤ g⁻¹ :=
    (one_le_inv_iff₀).2 ⟨hg, hgOne⟩
  have hinvPow : 1 ≤ g⁻¹ ^ 6 := one_le_pow₀ hinv
  have hcard := freeTimeGrid_card_le_polynomial_clean T g hT hg
  have hcard' :
      (freeTimeGridCard T g : Real) ≤
        2 * (65536 * T + 1) * g⁻¹ ^ 6 := by
    calc
      (freeTimeGridCard T g : Real) ≤
          2 * (65536 * T * g⁻¹ ^ 6 + 1) := hcard
      _ ≤ 2 * (65536 * T + 1) * g⁻¹ ^ 6 := by
        nlinarith
  have hexponent :
      -(N j : Real) * g ^ 8 / 96 =
        -(1 / 96 : Real) * (N j : Real) * g ^ 8 := by
    ring
  calc
    freeGridBadBudget T (inverseLinearCoupling j) (N j) =
        2 * (N j : Real) * (freeTimeGridCard T g : Real) *
          Real.exp (-(N j : Real) * g ^ 8 / 96) := by rfl
    _ ≤ 2 * (N j : Real) *
          (2 * (65536 * T + 1) * g⁻¹ ^ 6) *
          Real.exp (-(N j : Real) * g ^ 8 / 96) := by
      gcongr
    _ = 4 * (65536 * T + 1) *
          concentrationUnionCost (1 / 96) N j := by
      rw [hexponent]
      unfold concentrationUnionCost
      dsimp [g]
      ring

/-- The explicit bad budget tends to zero for every volume schedule above
the inverse-twelfth-power floor, with no upper-volume hypothesis. -/
theorem freeGridBadBudget_tendsto_zero_clean
    (T : Real) (hT : 0 ≤ T) (N : Nat → Nat)
    (hN : ∀ j,
      inverseTwelfthPowerCeiling (inverseLinearCoupling j) ≤ N j) :
    Tendsto
      (fun j ↦ freeGridBadBudget T (inverseLinearCoupling j) (N j))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _j ↦ by
      unfold freeGridBadBudget
      positivity
  · exact Filter.Eventually.of_forall fun j ↦
      freeGridBadBudget_le_concentrationUnionCost_clean T hT N j
  · have hcost := supervolume_concentration_cost_tendsto_zero
      (1 / 96) (by norm_num) N hN
    have hmul := hcost.const_mul (4 * (65536 * T + 1))
    simpa only [concentrationUnionCost, mul_zero] using hmul

/-- Physical volume used by `scaledDistance` along the legal joint path. -/
def physicalSupervolumeSize (sizeCutoff : Real → Nat) (j : Nat) : Nat :=
  (supervolumeJointLimit sizeCutoff).systemSize j + 3

instance physicalSupervolumeSize_neZero
    (sizeCutoff : Real → Nat) (j : Nat) :
    NeZero (physicalSupervolumeSize sizeCutoff j) :=
  ⟨by unfold physicalSupervolumeSize; omega⟩

theorem physicalSupervolumeSize_ge_inverseTwelfthPower
    (sizeCutoff : Real → Nat) (j : Nat) :
    inverseTwelfthPowerCeiling (inverseLinearCoupling j) ≤
      physicalSupervolumeSize sizeCutoff j := by
  exact ((Nat.le_max_right _ _).trans
    (supervolumeSystemSize_ge_requestedFloor sizeCutoff j)).trans
      (Nat.le_add_right _ 3)

theorem physicalSupervolume_freeGridBadBudget_tendsto_zero_clean
    (sizeCutoff : Real → Nat) (T : Real) (hT : 0 ≤ T) :
    Tendsto
      (fun j ↦ freeGridBadBudget T (inverseLinearCoupling j)
        (physicalSupervolumeSize sizeCutoff j))
      atTop (nhds 0) := by
  exact freeGridBadBudget_tendsto_zero_clean T hT
    (physicalSupervolumeSize sizeCutoff)
    (physicalSupervolumeSize_ge_inverseTwelfthPower sizeCutoff)

/-- The exact complement-measure interface consumed by the generic
uniform-window event compositor. -/
theorem physicalSupervolumeSignedFreeGridGood_compl_measureReal_tendsto_zero
    (sizeCutoff : Real → Nat) (T : Real) (hT : 0 ≤ T) :
    Tendsto
      (fun j ↦ canonicalIIDMassPhaseEnsemble.probability.real
        (canonicalPhysicalSignedFreeGridGood
          (N := physicalSupervolumeSize sizeCutoff j)
          T (inverseLinearCoupling j))ᶜ)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _j ↦ measureReal_nonneg
  · exact Filter.Eventually.of_forall fun j ↦
      canonicalPhysicalSignedFreeGridGood_compl_measureReal_le
        (N := physicalSupervolumeSize sizeCutoff j)
        (by unfold physicalSupervolumeSize; omega) T
        (inverseLinearCoupling j)
  · exact physicalSupervolume_freeGridBadBudget_tendsto_zero_clean
      sizeCutoff T hT

/-- Along the legal physical supervolume path, the one measurable
physical-sign grid-good event has probability tending to one.  There is no
upper bound on the chosen volume. -/
theorem physicalSupervolumeSignedFreeGridGood_probability_tendsto_one
    (sizeCutoff : Real → Nat) (T : Real) (hT : 0 ≤ T) :
    Tendsto
      (fun j ↦ canonicalIIDMassPhaseEnsemble.probability
        (canonicalPhysicalSignedFreeGridGood
          (N := physicalSupervolumeSize sizeCutoff j)
          T (inverseLinearCoupling j)))
      atTop (nhds 1) := by
  let goodEvent : Nat → Set RandomEnsemble.SampleSpace := fun j ↦
    canonicalPhysicalSignedFreeGridGood
      (N := physicalSupervolumeSize sizeCutoff j)
      T (inverseLinearCoupling j)
  let badBudget : Nat → Real := fun j ↦
    freeGridBadBudget T (inverseLinearCoupling j)
      (physicalSupervolumeSize sizeCutoff j)
  have hbadReal :
      Tendsto
        (fun j ↦ canonicalIIDMassPhaseEnsemble.probability.real
          (goodEvent j)ᶜ) atTop (nhds 0) := by
    exact
      physicalSupervolumeSignedFreeGridGood_compl_measureReal_tendsto_zero
        sizeCutoff T hT
  have hbadENNReal :
      Tendsto
        (fun j ↦ canonicalIIDMassPhaseEnsemble.probability
          (goodEvent j)ᶜ) atTop (nhds 0) := by
    have hofReal := ENNReal.tendsto_ofReal hbadReal
    have hfun :
        (fun j ↦ ENNReal.ofReal
          (canonicalIIDMassPhaseEnsemble.probability.real
            (goodEvent j)ᶜ)) =
        (fun j ↦ canonicalIIDMassPhaseEnsemble.probability
          (goodEvent j)ᶜ) := by
      funext j
      exact ofReal_measureReal
        (measure_ne_top canonicalIIDMassPhaseEnsemble.probability _)
    rw [hfun, ENNReal.ofReal_zero] at hofReal
    exact hofReal
  have hsub := ENNReal.Tendsto.sub
    (tendsto_const_nhds :
      Tendsto (fun _j : Nat ↦ (1 : ENNReal)) atTop (nhds 1))
    hbadENNReal (Or.inl ENNReal.one_ne_top)
  have hmeasureIdentity :
      (fun j ↦ canonicalIIDMassPhaseEnsemble.probability
        (goodEvent j)) =
      (fun j ↦ 1 - canonicalIIDMassPhaseEnsemble.probability
        (goodEvent j)ᶜ) := by
    funext j
    calc
      canonicalIIDMassPhaseEnsemble.probability (goodEvent j) =
          canonicalIIDMassPhaseEnsemble.probability ((goodEvent j)ᶜ)ᶜ := by
        simp only [compl_compl]
      _ = canonicalIIDMassPhaseEnsemble.probability Set.univ -
          canonicalIIDMassPhaseEnsemble.probability (goodEvent j)ᶜ :=
        measure_compl
          (measurableSet_canonicalPhysicalSignedFreeGridGood
            (N := physicalSupervolumeSize sizeCutoff j)
            T (inverseLinearCoupling j)).compl
          (measure_ne_top canonicalIIDMassPhaseEnsemble.probability _)
      _ = 1 - canonicalIIDMassPhaseEnsemble.probability
          (goodEvent j)ᶜ := by rw [measure_univ]
  change Tendsto
    (fun j ↦ canonicalIIDMassPhaseEnsemble.probability (goodEvent j))
    atTop (nhds 1)
  rw [hmeasureIdentity]
  simpa using hsub

#print axioms physicalSignedHaarBondField_fixedTime_tail
#print axioms physicalSignedFreeGridBadAtMass_measureReal_le
#print axioms canonicalPhysicalSignedSimpleFreeGridBad_measureReal_le
#print axioms canonicalPhysicalSignedFreeGridGood_compl_measureReal_le
#print axioms physicalSupervolumeSignedFreeGridGood_compl_measureReal_tendsto_zero
#print axioms physicalSupervolumeSignedFreeGridGood_probability_tendsto_one

end

end ArchonPhysics.R32PhysicalSignedFreeBondConcentrationV3
