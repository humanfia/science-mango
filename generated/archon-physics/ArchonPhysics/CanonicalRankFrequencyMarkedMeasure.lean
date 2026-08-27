import ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
import ArchonPhysics.OrderedTranslationLastMode

/-!
# Canonical rank-frequency marked measures

The joint-frequency collision measure forgets which ordered spectral ranks
carry its three frequencies.  This module retains, on every leg, the pair
`(k / N, omega_k)`, where `k` is the decreasing ordered spectral rank and
`N` is the lattice volume.  It constructs the corresponding finite weighted
Dirac measure and its canonical per-site rescaling.

Forgetting ranks recovers the existing joint-frequency measure exactly.  All
marks lie in the volume-independent compact box
`([0, 1] x [0, sqrt 5])^3`, and all three coordinates retain exact `S_3`
permutation symmetry.  These are finite-volume statements only; no marked
thermodynamic weak limit is asserted.
-/

open scoped Topology

namespace ArchonPhysics.CanonicalRankFrequencyMarkedMeasure

open ArchonPhysics
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Thermodynamic mode mark: normalized ordered rank and harmonic frequency. -/
abbrev RankFrequencyMark := Real × Real

namespace RankFrequencyMark

def rank (mark : RankFrequencyMark) : Real := mark.1

def frequency (mark : RankFrequencyMark) : Real := mark.2

end RankFrequencyMark

/-- Ordered spectral rank divided by the lattice volume. -/
def normalizedOrderedRank {N : Nat} [NeZero N]
    (k : OrderedModeIndex N) : Real :=
  (k.val : Real) / (N : Real)

theorem normalizedOrderedRank_nonneg {N : Nat} [NeZero N]
    (k : OrderedModeIndex N) :
    0 <= normalizedOrderedRank k := by
  unfold normalizedOrderedRank
  positivity

/-- Every finite-volume ordered rank lies strictly below one after volume
normalization. -/
theorem normalizedOrderedRank_lt_one {N : Nat} [NeZero N]
    (k : OrderedModeIndex N) :
    normalizedOrderedRank k < 1 := by
  have hNnat : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hkNat : k.val < N := by
    simpa [Lattice.Site, ZMod.card] using k.isLt
  have hN : (0 : Real) < (N : Real) := by
    exact_mod_cast hNnat
  unfold normalizedOrderedRank
  exact (div_lt_one hN).2 (by exact_mod_cast hkNat)

/-- Rank-frequency mark of one ordered harmonic mode. -/
def orderedRankFrequencyMark {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : OrderedModeIndex N) :
    RankFrequencyMark :=
  (normalizedOrderedRank k,
    orderedModeFrequency (harmonicHermitian m) k)

/-- Three marked legs carried by one ordered mode triple. -/
def orderedRankFrequencyTriple {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (modes : OrderedModeTriple N) :
    Fin 3 -> RankFrequencyMark :=
  fun r => orderedRankFrequencyMark m (modes r)

/-- Forget the rank coordinate on a marked three-leg tuple. -/
def forgetRankFrequencyTriple
    (marks : Fin 3 -> RankFrequencyMark) : Fin 3 -> Real :=
  fun r => (marks r).2

theorem continuous_forgetRankFrequencyTriple :
    Continuous forgetRankFrequencyTriple := by
  unfold forgetRankFrequencyTriple
  fun_prop

theorem measurable_forgetRankFrequencyTriple :
    Measurable forgetRankFrequencyTriple :=
  continuous_forgetRankFrequencyTriple.measurable

@[simp] theorem forgetRankFrequencyTriple_orderedRankFrequencyTriple
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) :
    forgetRankFrequencyTriple (orderedRankFrequencyTriple m modes) =
      orderedFrequencyTriple m modes := by
  rfl

/-- Positive normalized collision weight placed at each ordered marked
rank-frequency triple. -/
def positiveWeightedRankFrequencyTripleMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    Measure (Fin 3 -> RankFrequencyMark) := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes then
      ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) •
        Measure.dirac (orderedRankFrequencyTriple m modes)
    else 0

theorem positiveWeightedRankFrequencyTripleMeasure_isFinite
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    IsFiniteMeasure (positiveWeightedRankFrequencyTripleMeasure m) := by
  constructor
  unfold positiveWeightedRankFrequencyTripleMeasure
  classical
  simp only [Measure.coe_finsetSum, Finset.sum_apply, ENNReal.sum_lt_top,
    Finset.mem_univ, forall_const]
  intro modes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · simp [hpositive]
  · simp [hpositive]

/-- Bundled fixed-volume marked collision measure. -/
def positiveWeightedRankFrequencyTripleFiniteMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    FiniteMeasure (Fin 3 -> RankFrequencyMark) :=
  ⟨positiveWeightedRankFrequencyTripleMeasure m,
    positiveWeightedRankFrequencyTripleMeasure_isFinite m⟩

/-- Forgetting all three rank coordinates recovers the existing raw joint
frequency measure exactly. -/
theorem map_positiveWeightedRankFrequencyTripleMeasure_forgetRank
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    (positiveWeightedRankFrequencyTripleMeasure m).map
        forgetRankFrequencyTriple =
      positiveWeightedFrequencyTripleMeasure m := by
  classical
  unfold positiveWeightedRankFrequencyTripleMeasure
    positiveWeightedFrequencyTripleMeasure
  rw [Measure.map_finset_sum'
    measurable_forgetRankFrequencyTriple.aemeasurable]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · simp only [if_pos hpositive]
    rw [Measure.map_smul,
      Measure.map_dirac' measurable_forgetRankFrequencyTriple]
    rw [forgetRankFrequencyTriple_orderedRankFrequencyTriple]
  · simp [hpositive]

/-- Bundled finite-measure form of the exact forgetful pushforward. -/
theorem map_positiveWeightedRankFrequencyTripleFiniteMeasure_forgetRank
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    (positiveWeightedRankFrequencyTripleFiniteMeasure m).map
        forgetRankFrequencyTriple =
      positiveWeightedFrequencyTripleFiniteMeasure m := by
  apply FiniteMeasure.toMeasure_injective
  exact map_positiveWeightedRankFrequencyTripleMeasure_forgetRank m

/-- Canonical per-site marked measure at volume `N = n + 2`. -/
def canonicalRankFrequencyTriplePerSiteFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    FiniteMeasure (Fin 3 -> RankFrequencyMark) :=
  (((n + 2 : Nat) : NNReal)⁻¹) •
    positiveWeightedRankFrequencyTripleFiniteMeasure
      (ensemble.restrictPositiveMass (N := n + 2) omega)

/-- Forgetting ranks commutes exactly with canonical per-site rescaling. -/
theorem map_canonicalRankFrequencyTriplePerSiteFiniteMeasure_forgetRank
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble n omega).map forgetRankFrequencyTriple =
      canonicalJointFrequencyPerSiteFiniteMeasure ensemble n omega := by
  unfold canonicalRankFrequencyTriplePerSiteFiniteMeasure
    canonicalJointFrequencyPerSiteFiniteMeasure
  rw [FiniteMeasure.map_smul,
    map_positiveWeightedRankFrequencyTripleFiniteMeasure_forgetRank]

/-- Uniform compact box `([0,1] x [0,sqrt 5])^3` for the marked tuples. -/
def collisionRankFrequencyTripleSupport :
    Set (Fin 3 -> RankFrequencyMark) :=
  Set.Icc (fun _ => (0, 0))
    (fun _ => (1, collisionFrequencyCeiling))

theorem collisionRankFrequencyTripleSupport_isCompact :
    IsCompact collisionRankFrequencyTripleSupport := by
  exact isCompact_Icc

/-- Every ordered marked tuple of every canonical iid realization belongs to
the common compact rank-frequency box. -/
theorem iid_orderedRankFrequencyTriple_mem_uniformSupport
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (modes : OrderedModeTriple N) :
    orderedRankFrequencyTriple
        (ensemble.restrictPositiveMass (N := N) omega) modes ∈
      collisionRankFrequencyTripleSupport := by
  constructor
  · intro r
    exact ⟨normalizedOrderedRank_nonneg (modes r),
      (iid_orderedModeFrequency_mem_uniformBand
        ensemble omega (modes r)).1⟩
  · intro r
    exact ⟨(normalizedOrderedRank_lt_one (modes r)).le,
      (iid_orderedModeFrequency_mem_uniformBand
        ensemble omega (modes r)).2⟩

/-- The raw marked measure has no mass outside the common compact box. -/
theorem iid_positiveWeightedRankFrequencyTripleMeasure_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) :
    positiveWeightedRankFrequencyTripleMeasure
        (ensemble.restrictPositiveMass (N := N) omega)
        (collisionRankFrequencyTripleSupportᶜ) = 0 := by
  classical
  unfold positiveWeightedRankFrequencyTripleMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple
      (ensemble.restrictPositiveMass (N := N) omega) modes
  · rw [if_pos hpositive, Measure.smul_apply]
    simp [iid_orderedRankFrequencyTriple_mem_uniformSupport
      ensemble omega modes]
  · rw [if_neg hpositive]
    rfl

/-- Per-site scaling preserves the common compact marked support. -/
theorem canonicalRankFrequencyTriplePerSiteFiniteMeasure_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) :
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega :
        Measure (Fin 3 -> RankFrequencyMark))
      (collisionRankFrequencyTripleSupportᶜ) = 0 := by
  unfold canonicalRankFrequencyTriplePerSiteFiniteMeasure
  rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply]
  change _ * positiveWeightedRankFrequencyTripleMeasure
      (ensemble.restrictPositiveMass (N := n + 2) omega)
      (collisionRankFrequencyTripleSupportᶜ) = 0
  rw [iid_positiveWeightedRankFrequencyTripleMeasure_compl_uniformSupport_eq_zero
    ensemble omega]
  simp

/-! ## Exact coordinate-permutation symmetry -/

/-- Coordinate permutation on marked triples. -/
def permuteRankFrequencyTriple (e : Equiv.Perm (Fin 3))
    (marks : Fin 3 -> RankFrequencyMark) :
    Fin 3 -> RankFrequencyMark :=
  marks ∘ e

theorem continuous_permuteRankFrequencyTriple (e : Equiv.Perm (Fin 3)) :
    Continuous (permuteRankFrequencyTriple e) := by
  unfold permuteRankFrequencyTriple
  fun_prop

theorem measurable_permuteRankFrequencyTriple (e : Equiv.Perm (Fin 3)) :
    Measurable (permuteRankFrequencyTriple e) :=
  (continuous_permuteRankFrequencyTriple e).measurable

/-- Reindexing equivalence on complete ordered mode triples. -/
def permuteOrderedModeTriple {N : Nat} [NeZero N]
    (e : Equiv.Perm (Fin 3)) : OrderedModeTriple N ≃ OrderedModeTriple N where
  toFun modes := modes ∘ e
  invFun modes := modes ∘ e.symm
  left_inv modes := by
    funext r
    simp [Function.comp_apply]
  right_inv modes := by
    funext r
    simp [Function.comp_apply]

theorem harmonicOrderedInteractionWeightSq_perm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (e : Equiv.Perm (Fin 3)) :
    harmonicOrderedInteractionWeightSq m (modes ∘ e) =
      harmonicOrderedInteractionWeightSq m modes := by
  unfold harmonicOrderedInteractionWeightSq orderedInteractionWeightSq
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro l _hl
  exact Equiv.prod_comp e
    (fun r => projectedBondKernel (massWeightedDifferenceMatrix m)
      (harmonicHermitian m) (modes r) j l)

theorem harmonicOrderedNormalizedInteractionWeight_perm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (e : Equiv.Perm (Fin 3)) :
    harmonicOrderedNormalizedInteractionWeight m (modes ∘ e) =
      harmonicOrderedNormalizedInteractionWeight m modes := by
  unfold harmonicOrderedNormalizedInteractionWeight
  rw [harmonicOrderedInteractionWeightSq_perm]
  congr 1
  exact Equiv.prod_comp e
    (fun r =>
      (2 * orderedModeFrequency (harmonicHermitian m) (modes r))⁻¹)

theorem isPositiveOrderedTriple_perm_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (e : Equiv.Perm (Fin 3)) :
    IsPositiveOrderedTriple m (modes ∘ e) ↔
      IsPositiveOrderedTriple m modes := by
  constructor
  · intro h r
    simpa [Function.comp_apply] using h (e.symm r)
  · intro h r
    exact h (e r)

@[simp] theorem orderedRankFrequencyTriple_comp_perm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (e : Equiv.Perm (Fin 3)) :
    orderedRankFrequencyTriple m (modes ∘ e) =
      permuteRankFrequencyTriple e (orderedRankFrequencyTriple m modes) := by
  rfl

/-- The fixed-volume marked finite measure is invariant under every
permutation of its three legs. -/
theorem map_positiveWeightedRankFrequencyTripleFiniteMeasure_perm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (e : Equiv.Perm (Fin 3)) :
    (positiveWeightedRankFrequencyTripleFiniteMeasure m).map
        (permuteRankFrequencyTriple e) =
      positiveWeightedRankFrequencyTripleFiniteMeasure m := by
  classical
  apply FiniteMeasure.toMeasure_injective
  change
    (positiveWeightedRankFrequencyTripleMeasure m).map
        (permuteRankFrequencyTriple e) =
      positiveWeightedRankFrequencyTripleMeasure m
  unfold positiveWeightedRankFrequencyTripleMeasure
  rw [Measure.map_finset_sum'
    (measurable_permuteRankFrequencyTriple e).aemeasurable]
  calc
    (∑ modes : OrderedModeTriple N,
        Measure.map (permuteRankFrequencyTriple e)
          (if IsPositiveOrderedTriple m modes then
            ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) •
              Measure.dirac (orderedRankFrequencyTriple m modes)
          else 0)) =
      ∑ modes : OrderedModeTriple N,
        (if IsPositiveOrderedTriple m (modes ∘ e) then
          ENNReal.ofReal
              (harmonicOrderedNormalizedInteractionWeight m (modes ∘ e)) •
            Measure.dirac (orderedRankFrequencyTriple m (modes ∘ e))
        else 0) := by
          apply Finset.sum_congr rfl
          intro modes _hmodes
          by_cases hpositive : IsPositiveOrderedTriple m modes
          · rw [if_pos hpositive,
              if_pos ((isPositiveOrderedTriple_perm_iff m modes e).2 hpositive),
              Measure.map_smul,
              Measure.map_dirac' (measurable_permuteRankFrequencyTriple e)]
            rw [harmonicOrderedNormalizedInteractionWeight_perm,
              orderedRankFrequencyTriple_comp_perm]
          · rw [if_neg hpositive,
              if_neg (mt (isPositiveOrderedTriple_perm_iff m modes e).1 hpositive)]
            simp
    _ = ∑ modes : OrderedModeTriple N,
        (if IsPositiveOrderedTriple m modes then
          ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) •
            Measure.dirac (orderedRankFrequencyTriple m modes)
        else 0) := by
          exact Equiv.sum_comp (permuteOrderedModeTriple e)
            (fun modes : OrderedModeTriple N =>
              if IsPositiveOrderedTriple m modes then
                ENNReal.ofReal
                    (harmonicOrderedNormalizedInteractionWeight m modes) •
                  Measure.dirac (orderedRankFrequencyTriple m modes)
              else 0)

/-- Canonical per-site marked measures inherit exact full `S_3` symmetry. -/
theorem map_canonicalRankFrequencyTriplePerSiteFiniteMeasure_perm
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega)
    (e : Equiv.Perm (Fin 3)) :
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble n omega).map (permuteRankFrequencyTriple e) =
      canonicalRankFrequencyTriplePerSiteFiniteMeasure
        ensemble n omega := by
  unfold canonicalRankFrequencyTriplePerSiteFiniteMeasure
  rw [FiniteMeasure.map_smul,
    map_positiveWeightedRankFrequencyTripleFiniteMeasure_perm]

end

end ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
