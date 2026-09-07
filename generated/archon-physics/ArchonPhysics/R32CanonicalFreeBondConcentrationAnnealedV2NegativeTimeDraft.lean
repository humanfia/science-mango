import ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final

/-!
# Draft: annealed V2 signed free-bond tail at physical negative time

This file is a static, unbuilt proof draft.  It isolates the finite-time
probability part of the V2 compositor.  The physical free propagation uses
the backward phase advance, represented here by evaluating
`signedHaarBondField` at `-time`.  Fixed-time Haar concentration is unchanged
by that sign.

The proof uses only the initial product Haar law.  In particular, it does not
postulate independence of any positive- or negative-time field.
-/

namespace ArchonPhysics.R32CanonicalFreeBondConcentrationAnnealedV2NegativeTimeDraft

open ArchonPhysics
open ArchonPhysics.FiniteProductBoundedDifferences
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final
open ArchonPhysics.R32CanonicalProductTailTransferV2
open ArchonPhysics.R32HaarScalarTailCleanV4
open ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final
open ArchonPhysics.RandomPhaseMoments
open MeasureTheory ProbabilityTheory Set
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

/-! ## Backward free time and fixed-time tails -/

/-- The physical backward/free-flow convention: advance every Haar mode by
the negative of the displayed physical time. -/
def signedBackwardHaarBondField {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (bond : Lattice.Site N)
    (phase : HarmonicOrderedModeIndex N → UnitAddCircle)
    (time : Real) : Real :=
  signedHaarBondField m bond phase (-time)

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
  have hproxy_coe : (proxy : Real) = variance := rfl
  have hproxy : haarScalarVarianceProxy coefficient ≤ proxy := by
    apply NNReal.coe_le_coe.mp
    change (∑ k, coefficient k ^ 2) ≤ (proxy : Real)
    rw [hproxy_coe]
    exact hsum
  have hmgf : HasSubgaussianMGF
      (fixedTimeHaarScalarSum coefficient frequency time) proxy
      (finitePhaseHaarLaw (Fin n)) :=
    hasSubgaussianMGF_mono_parameter
      (hasSubgaussianMGF_fixedTimeHaarScalarSum
        coefficient frequency time) hproxy
  simpa only [hproxy_coe] using
    measureReal_abs_gt_le_of_hasSubgaussianMGF hmgf hu

/-- A signed-frame bond at one physical time has the inverse-volume tail.
The minus sign is passed directly to the fixed-time Haar theorem. -/
theorem signedBackwardHaarBondField_fixedTime_tail
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (bond : Lattice.Site N) (time : Real) {u : Real} (hu : 0 ≤ u) :
    (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
        {phase | |signedBackwardHaarBondField m bond phase time| > u} ≤
      2 * Real.exp
        (-u ^ 2 / (2 * (6 / (((N - 1 : Nat) : Real))))) := by
  have hpredNat : 0 < N - 1 := by omega
  have hpred : 0 < (((N - 1 : Nat) : Real)) := by
    exact_mod_cast hpredNat
  exact measureReal_abs_fixedTimeHaarScalarSum_gt_le_of_sum_sq_le
    (signedFrozenBondCoefficient m bond)
    (orderedModeFrequency (harmonicHermitian m)) (-time)
    (by positivity)
    (sum_sq_signedFrozenBondCoefficient_le_six_div_pred
      hN m hsimple bond) hu

/-- At threshold `g^4 / 2`, the one-bond, one-time failure probability is
`2 exp (-N g^8 / 96)`. -/
theorem signedBackwardHaarBondField_halfThreshold_tail
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (bond : Lattice.Site N) (time g : Real) :
    (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
        {phase |
          |signedBackwardHaarBondField m bond phase time| > g ^ 4 / 2} ≤
      2 * Real.exp (-(N : Real) * g ^ 8 / 96) := by
  have htail := signedBackwardHaarBondField_fixedTime_tail
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
  calc
    (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
        {phase |
          |signedBackwardHaarBondField m bond phase time| > g ^ 4 / 2} ≤
        2 * Real.exp
          (-(g ^ 4 / 2) ^ 2 /
            (2 * (6 / (((N - 1 : Nat) : Real))))) := htail
    _ = 2 * Real.exp
        (-(((N - 1 : Nat) : Real)) * g ^ 8 / 48) := by
      rw [hexponent]
    _ ≤ 2 * Real.exp (-(N : Real) * g ^ 8 / 96) := by
      gcongr

/-! ## Finite negative-time grid -/

/-- The negative-time image of the V2 positive kinetic grid. -/
def negativeFreeTimeGrid (T g : Real) : Fin (freeTimeGridCard T g) → Real :=
  fun index ↦ -(freeTimeGrid T g index)

/-- Failure on one bond and one negative-time grid point for a frozen mass. -/
def signedNegativeFreeGridBad {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (T g : Real) :
    Set (HarmonicOrderedModeIndex N → UnitAddCircle) :=
  ⋃ index : Lattice.Site N × Fin (freeTimeGridCard T g),
    {phase |
      |signedHaarBondField m index.1 phase
          (negativeFreeTimeGrid T g index.2)| > g ^ 4 / 2}

theorem measurableSet_signedNegativeFreeGridBad
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (T g : Real) :
    MeasurableSet (signedNegativeFreeGridBad m T g) := by
  unfold signedNegativeFreeGridBad
  apply MeasurableSet.iUnion
  intro index
  exact measurableSet_lt measurable_const
    (measurable_fixedTimeHaarScalarSum
      (signedFrozenBondCoefficient m index.1)
      (orderedModeFrequency (harmonicHermitian m))
      (negativeFreeTimeGrid T g index.2)).abs

/-- Quenched union bound over all bonds and all negative-time grid points. -/
theorem signedNegativeFreeGridBad_measureReal_le
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (T g : Real) :
    (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
        (signedNegativeFreeGridBad m T g) ≤
      freeGridBadBudget T g N := by
  unfold signedNegativeFreeGridBad
  calc
    (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
        (⋃ index : Lattice.Site N × Fin (freeTimeGridCard T g),
          {phase |
            |signedHaarBondField m index.1 phase
                (negativeFreeTimeGrid T g index.2)| > g ^ 4 / 2}) ≤
        ∑ index : Lattice.Site N × Fin (freeTimeGridCard T g),
          (finitePhaseHaarLaw (HarmonicOrderedModeIndex N)).real
            {phase |
              |signedHaarBondField m index.1 phase
                  (negativeFreeTimeGrid T g index.2)| > g ^ 4 / 2} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _index : Lattice.Site N × Fin (freeTimeGridCard T g),
        2 * Real.exp (-(N : Real) * g ^ 8 / 96) := by
      exact Finset.sum_le_sum fun index _ ↦
        signedBackwardHaarBondField_halfThreshold_tail
          hN m hsimple index.1 (freeTimeGrid T g index.2) g
    _ = freeGridBadBudget T g N := by
      simp [freeGridBadBudget, Fintype.card_prod]
      ring

/-! ## Exact phase sections and canonical product transfer -/

/-- The jointly Borel canonical event obtained by using the negative grid in
the generic measurable signed-frame event. -/
def canonicalSignedSimpleNegativeFreeGridBad
    {N : Nat} [NeZero N] (T g : Real) :
    Set RandomEnsemble.SampleSpace :=
  canonicalSignedSimpleGridBad
    (N := N) (negativeFreeTimeGrid T g) g

theorem measurableSet_canonicalSignedSimpleNegativeFreeGridBad
    {N : Nat} [NeZero N] (T g : Real) :
    MeasurableSet
      (canonicalSignedSimpleNegativeFreeGridBad (N := N) T g) :=
  measurableSet_canonicalSignedSimpleGridBad
    (negativeFreeTimeGrid T g) g

/-- For a frozen raw mass, the canonical negative-grid phase section is
exactly the pullback of the finite signed Haar event. -/
theorem phaseSection_canonicalSignedSimpleNegativeFreeGridBad_eq
    {N : Nat} [NeZero N]
    (T g : Real) (mass : RandomEnsemble.RawMassSequence)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (rawCanonicalFrozenMass (N := N) mass))) :
    Prod.mk mass ⁻¹'
        canonicalSignedSimpleNegativeFreeGridBad (N := N) T g =
      orderedPhaseBlockFromSequence (N := N) ⁻¹'
        signedNegativeFreeGridBad
          (rawCanonicalFrozenMass (N := N) mass) T g := by
  ext phase
  simp [canonicalSignedSimpleNegativeFreeGridBad,
    canonicalSignedSimpleGridBad, signedNegativeFreeGridBad,
    negativeFreeTimeGrid, hsimple]

/-- Every frozen raw-mass phase section obeys the same explicit bound; a
nonsimple-spectrum section is empty by construction. -/
theorem phaseSection_canonicalSignedSimpleNegativeFreeGridBad_measureReal_le
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (T g : Real) (mass : RandomEnsemble.RawMassSequence) :
    RandomEnsemble.phaseSequenceLaw.real
        (Prod.mk mass ⁻¹'
          canonicalSignedSimpleNegativeFreeGridBad (N := N) T g) ≤
      freeGridBadBudget T g N := by
  by_cases hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (rawCanonicalFrozenMass (N := N) mass))
  · rw [phaseSection_canonicalSignedSimpleNegativeFreeGridBad_eq
      T g mass hsimple, measureReal_def]
    have hmeasure :=
      (orderedPhaseBlockFromSequence_hasLaw (N := N)).measure_eq
        (measurableSet_signedNegativeFreeGridBad
          (rawCanonicalFrozenMass (N := N) mass) T g)
    change
      (RandomEnsemble.phaseSequenceLaw
        {phase |
          orderedPhaseBlockFromSequence (N := N) phase ∈
            signedNegativeFreeGridBad
              (rawCanonicalFrozenMass (N := N) mass) T g}).toReal ≤ _
    calc
      _ = ((finitePhaseHaarLaw (HarmonicOrderedModeIndex N))
          (signedNegativeFreeGridBad
            (rawCanonicalFrozenMass (N := N) mass) T g)).toReal :=
        congrArg ENNReal.toReal hmeasure
      _ ≤ freeGridBadBudget T g N := by
        rw [← measureReal_def]
        exact signedNegativeFreeGridBad_measureReal_le hN
          (rawCanonicalFrozenMass (N := N) mass) hsimple T g
  · have hevent :
        Prod.mk mass ⁻¹'
          canonicalSignedSimpleNegativeFreeGridBad (N := N) T g = ∅ := by
      ext phase
      simp [canonicalSignedSimpleNegativeFreeGridBad,
        canonicalSignedSimpleGridBad, hsimple]
    rw [hevent]
    simp [freeGridBadBudget]
    positivity

/-- Annealed canonical negative-grid tail.  Joint measurability is discharged
by the signed first-positive-pivot eigenframe module, not assumed. -/
theorem canonicalSignedSimpleNegativeFreeGridBad_measureReal_le
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (T g : Real) :
    canonicalIIDMassPhaseEnsemble.probability.real
        (canonicalSignedSimpleNegativeFreeGridBad (N := N) T g) ≤
      freeGridBadBudget T g N := by
  exact canonical_measureReal_le_of_phase_sections
    (canonicalSignedSimpleNegativeFreeGridBad (N := N) T g)
    (measurableSet_canonicalSignedSimpleNegativeFreeGridBad T g)
    (phaseSection_canonicalSignedSimpleNegativeFreeGridBad_measureReal_le
      hN T g)

#print axioms signedBackwardHaarBondField_fixedTime_tail
#print axioms signedNegativeFreeGridBad_measureReal_le
#print axioms phaseSection_canonicalSignedSimpleNegativeFreeGridBad_measureReal_le
#print axioms canonicalSignedSimpleNegativeFreeGridBad_measureReal_le

end

end ArchonPhysics.R32CanonicalFreeBondConcentrationAnnealedV2NegativeTimeDraft
