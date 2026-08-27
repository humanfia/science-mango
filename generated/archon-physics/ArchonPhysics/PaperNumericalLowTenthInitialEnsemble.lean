import ArchonPhysics.FiniteEnsemblePhaseMoments
import ArchonPhysics.OrderedPositiveInitialEnergyProfile

/-!
# A truth-audited low-ten-percent numerical initial ensemble

This file records a periodic-chain variant of the numerical initialization
described informally as exciting the lowest roughly ten percent of the normal
modes.  For `M = N - 1` positive ordered modes we make the rounding convention
fully explicit:

`K(M) = max 1 (M / 10)`.

The last `K(M)` positive ordered indices receive equal energy.  These are the
lowest positive frequencies because the ordered spectrum is descending and its
final index is the translation zero mode.  All other modes receive zero energy.
modal energy is exactly `N * epsilon`.

The random masses use the pre-existing paper-faithful canonical law: iid
uniform coordinates on `[4/5, 6/5]`.  The phases are iid normalized Haar and
independent of the masses.  The boundary convention in the source paper is
not sufficiently explicit for us to identify it theorem-for-theorem, so this
module deliberately claims only a periodic-boundary variant.

The modal radii are deterministic once the energy density is fixed.  Product
Haar phases at fixed radii are **not** a circular complex-Gaussian law and do
not imply Wick factorization or nonlinear RPA propagation.  This module is an
exact initial-law and finite-spectrum result only; it does not assert a
microscopic-to-kinetic limit or thermalization.
-/

namespace ArchonPhysics.PaperNumericalLowTenthInitialEnsemble

open MeasureTheory ProbabilityTheory
open ArchonPhysics
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.RandomPhaseMoments
open scoped BigOperators

noncomputable section

/-! ## The deterministic positive-mode profile -/

/-- Number of excited modes among `M` positive ordered modes.  Natural-number
division is floor division, while `max 1` prevents an empty excitation band in
small nonempty volumes. -/
def excitedPositiveModeCount (M : Nat) : Nat :=
  max 1 (M / 10)

theorem excitedPositiveModeCount_pos (M : Nat) :
    0 < excitedPositiveModeCount M := by
  unfold excitedPositiveModeCount
  omega

theorem excitedPositiveModeCount_le {M : Nat} (hM : 1 <= M) :
    excitedPositiveModeCount M <= M := by
  have hdiv : M / 10 <= M := Nat.div_le_self M 10
  unfold excitedPositiveModeCount
  omega

theorem excitedPositiveModeCount_lt {M : Nat} (hM : 2 <= M) :
    excitedPositiveModeCount M < M := by
  have hdiv : M / 10 < M := Nat.div_lt_self (by omega) (by norm_num)
  unfold excitedPositiveModeCount
  omega

/-- The last `K(M)` positive ordered ranks.  Since the ordered eigenvalues
are descending and the translation zero mode is appended after these `M`
positive ranks, this tail is the lowest-positive-frequency sector. -/
def excitedPositiveModes (M : Nat) : Finset (Fin M) :=
  Finset.univ.filter fun mode =>
    M - excitedPositiveModeCount M <= mode.val

/-- The complementary, higher-frequency positive ordered ranks. -/
def unexcitedPositiveModes (M : Nat) : Finset (Fin M) :=
  Finset.univ.filter fun mode =>
    mode.val < M - excitedPositiveModeCount M

theorem card_unexcitedPositiveModes {M : Nat} (_hM : 1 <= M) :
    (unexcitedPositiveModes M).card =
      M - excitedPositiveModeCount M := by
  simpa [unexcitedPositiveModes,
    Nat.min_eq_right (Nat.sub_le M (excitedPositiveModeCount M))] using
    (Fin.card_filter_val_lt
      (n := M) (m := M - excitedPositiveModeCount M))

theorem card_excitedPositiveModes {M : Nat} (hM : 1 <= M) :
    (excitedPositiveModes M).card = excitedPositiveModeCount M := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin M)))
    (fun mode => mode.val < M - excitedPositiveModeCount M)
  rw [show (Finset.univ.filter fun mode : Fin M =>
      mode.val < M - excitedPositiveModeCount M) =
        unexcitedPositiveModes M by rfl,
    show (Finset.univ.filter fun mode : Fin M =>
      ¬ mode.val < M - excitedPositiveModeCount M) =
        excitedPositiveModes M by
          ext mode
          simp [excitedPositiveModes],
    card_unexcitedPositiveModes hM, Finset.card_univ,
    Fintype.card_fin] at h
  have hKle := excitedPositiveModeCount_le hM
  omega

theorem excited_union_unexcited (M : Nat) :
    excitedPositiveModes M ∪ unexcitedPositiveModes M = Finset.univ := by
  ext mode
  simp only [excitedPositiveModes, unexcitedPositiveModes,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun _ => True.intro
  · intro _
    omega

theorem disjoint_excited_unexcited (M : Nat) :
    Disjoint (excitedPositiveModes M) (unexcitedPositiveModes M) := by
  rw [Finset.disjoint_left]
  simp [excitedPositiveModes, unexcitedPositiveModes]

/-- The final positive ordered rank is in the excited low-frequency tail. -/
theorem last_positive_rank_mem_excited {M : Nat} (hM : 1 <= M)
    (mode : Fin M) (hmode : mode.val = M - 1) :
    mode ∈ excitedPositiveModes M := by
  simp only [excitedPositiveModes, Finset.mem_filter, Finset.mem_univ,
    true_and]
  have hKle := excitedPositiveModeCount_le hM
  have hKpos := excitedPositiveModeCount_pos M
  omega
/-- Equal energy on the lowest-frequency tail of `K(M)` positive modes and zero elsewhere. -/
def lowTenthPositiveEnergyProfile (M : Nat) (mode : Fin M) : Real :=
  if M - excitedPositiveModeCount M <= mode.val then
    1 / (excitedPositiveModeCount M : Real)
  else 0

theorem lowTenthPositiveEnergyProfile_nonneg (M : Nat) (mode : Fin M) :
    0 <= lowTenthPositiveEnergyProfile M mode := by
  rw [lowTenthPositiveEnergyProfile]
  split_ifs
  · positivity
  · exact le_rfl

theorem sum_excited_lowTenthPositiveEnergyProfile {M : Nat}
    (hM : 1 <= M) :
    (∑ mode ∈ excitedPositiveModes M,
      lowTenthPositiveEnergyProfile M mode) = 1 := by
  have hKne : (excitedPositiveModeCount M : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt (excitedPositiveModeCount_pos M))
  calc
    (∑ mode ∈ excitedPositiveModes M,
        lowTenthPositiveEnergyProfile M mode) =
        ∑ _mode ∈ excitedPositiveModes M,
          1 / (excitedPositiveModeCount M : Real) := by
      apply Finset.sum_congr rfl
      intro mode hmode
      rw [lowTenthPositiveEnergyProfile, if_pos]
      simpa [excitedPositiveModes] using hmode
    _ = (excitedPositiveModeCount M : Real) *
        (1 / (excitedPositiveModeCount M : Real)) := by
      simp only [Finset.sum_const, card_excitedPositiveModes hM,
        nsmul_eq_mul]
    _ = 1 := by field_simp

theorem sum_unexcited_lowTenthPositiveEnergyProfile (M : Nat) :
    (∑ mode ∈ unexcitedPositiveModes M,
      lowTenthPositiveEnergyProfile M mode) = 0 := by
  apply Finset.sum_eq_zero
  intro mode hmode
  rw [lowTenthPositiveEnergyProfile, if_neg]
  exact Nat.not_le.mpr (by simpa [unexcitedPositiveModes] using hmode)

/-- The positive-mode shape is a probability profile. -/
theorem sum_lowTenthPositiveEnergyProfile_eq_one {M : Nat}
    (hM : 1 <= M) :
    (∑ mode : Fin M, lowTenthPositiveEnergyProfile M mode) = 1 := by
  have hsum := Finset.sum_union
    (f := lowTenthPositiveEnergyProfile M)
    (disjoint_excited_unexcited M)
  rw [excited_union_unexcited] at hsum
  rw [hsum, sum_excited_lowTenthPositiveEnergyProfile hM,
    sum_unexcited_lowTenthPositiveEnergyProfile, add_zero]

/-- Exact `l1` distance of the low-ten-percent profile from equipartition on
the `M` positive modes. -/
theorem lowTenthPositiveEnergyProfile_l1_eq {M : Nat} (hM : 1 <= M) :
    (∑ mode : Fin M,
      |lowTenthPositiveEnergyProfile M mode - 1 / (M : Real)|) =
      2 * (1 - (excitedPositiveModeCount M : Real) / (M : Real)) := by
  have hKpos : 0 < (excitedPositiveModeCount M : Real) := by
    exact_mod_cast excitedPositiveModeCount_pos M
  have hMpos : 0 < (M : Real) := by positivity
  have hKle : excitedPositiveModeCount M <= M :=
    excitedPositiveModeCount_le hM
  have hKleReal : (excitedPositiveModeCount M : Real) <= (M : Real) := by
    exact_mod_cast hKle
  have hinv : 1 / (M : Real) <=
      1 / (excitedPositiveModeCount M : Real) :=
    one_div_le_one_div_of_le hKpos hKleReal
  have hex :
      (∑ mode ∈ excitedPositiveModes M,
        |lowTenthPositiveEnergyProfile M mode - 1 / (M : Real)|) =
        1 - (excitedPositiveModeCount M : Real) / (M : Real) := by
    calc
      (∑ mode ∈ excitedPositiveModes M,
          |lowTenthPositiveEnergyProfile M mode - 1 / (M : Real)|) =
          ∑ _mode ∈ excitedPositiveModes M,
            (1 / (excitedPositiveModeCount M : Real) -
              1 / (M : Real)) := by
        apply Finset.sum_congr rfl
        intro mode hmode
        rw [lowTenthPositiveEnergyProfile, if_pos,
          abs_of_nonneg (sub_nonneg.mpr hinv)]
        simpa [excitedPositiveModes] using hmode
      _ = (excitedPositiveModeCount M : Real) *
          (1 / (excitedPositiveModeCount M : Real) -
            1 / (M : Real)) := by
        simp only [Finset.sum_const, card_excitedPositiveModes hM,
          nsmul_eq_mul]
      _ = 1 - (excitedPositiveModeCount M : Real) / (M : Real) := by
        field_simp
  have hun :
      (∑ mode ∈ unexcitedPositiveModes M,
        |lowTenthPositiveEnergyProfile M mode - 1 / (M : Real)|) =
        1 - (excitedPositiveModeCount M : Real) / (M : Real) := by
    calc
      (∑ mode ∈ unexcitedPositiveModes M,
          |lowTenthPositiveEnergyProfile M mode - 1 / (M : Real)|) =
          ∑ _mode ∈ unexcitedPositiveModes M, 1 / (M : Real) := by
        apply Finset.sum_congr rfl
        intro mode hmode
        rw [lowTenthPositiveEnergyProfile, if_neg]
        · simp [abs_of_pos hMpos]
        · exact Nat.not_le.mpr (by simpa [unexcitedPositiveModes] using hmode)
      _ = ((M - excitedPositiveModeCount M : Nat) : Real) *
          (1 / (M : Real)) := by
        simp only [Finset.sum_const, card_unexcitedPositiveModes hM,
          nsmul_eq_mul]
      _ = 1 - (excitedPositiveModeCount M : Real) / (M : Real) := by
        rw [Nat.cast_sub hKle]
        field_simp
  have hsum := Finset.sum_union
    (f := fun mode : Fin M =>
      |lowTenthPositiveEnergyProfile M mode - 1 / (M : Real)|)
    (disjoint_excited_unexcited M)
  rw [excited_union_unexcited] at hsum
  rw [hsum, hex, hun]
  ring

theorem lowTenthPositiveEnergyProfile_l1_pos {M : Nat} (hM : 2 <= M) :
    0 < ∑ mode : Fin M,
      |lowTenthPositiveEnergyProfile M mode - 1 / (M : Real)| := by
  rw [lowTenthPositiveEnergyProfile_l1_eq (by omega)]
  have hKltReal : (excitedPositiveModeCount M : Real) < (M : Real) := by
    exact_mod_cast excitedPositiveModeCount_lt hM
  have hratio : (excitedPositiveModeCount M : Real) / (M : Real) < 1 :=
    (div_lt_one (by positivity)).2 hKltReal
  linarith

/-! ## Lift to all periodic ordered modes -/

/-- Lift the positive-mode profile to `Fin N`, placing zero energy in the
last ordered translation mode. -/
def orderedLowTenthEnergyShape (N : Nat) (mode : Fin N) : Real :=
  if hmode : mode.val < N - 1 then
    lowTenthPositiveEnergyProfile (N - 1) ⟨mode.val, hmode⟩
  else 0

@[simp] theorem orderedLowTenthEnergyShape_last
    {N : Nat} [NeZero N] :
    orderedLowTenthEnergyShape N (lastSiteOrderedIndex N) = 0 := by
  simp [orderedLowTenthEnergyShape, lastSiteOrderedIndex]

theorem orderedLowTenthEnergyShape_nonneg
    (N : Nat) (mode : Fin N) :
    0 <= orderedLowTenthEnergyShape N mode := by
  rw [orderedLowTenthEnergyShape]
  split_ifs
  · exact lowTenthPositiveEnergyProfile_nonneg _ _
  · exact le_rfl

theorem sum_orderedLowTenthEnergyShape_eq_one
    {N : Nat} (hN : 2 <= N) :
    (∑ mode : Fin N, orderedLowTenthEnergyShape N mode) = 1 := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [Fin.sum_univ_castSucc]
  have hsum :
      (∑ mode : Fin M,
        orderedLowTenthEnergyShape M.succ mode.castSucc) =
        ∑ mode : Fin M, lowTenthPositiveEnergyProfile M mode := by
    apply Finset.sum_congr rfl
    intro mode _hmode
    have hlt : mode.castSucc.val < M.succ - 1 := by simp
    rw [orderedLowTenthEnergyShape, dif_pos hlt]
    rfl
  have hlast :
      orderedLowTenthEnergyShape M.succ (Fin.last M) = 0 := by
    simp [orderedLowTenthEnergyShape]
  rw [hsum, hlast, add_zero]
  exact sum_lowTenthPositiveEnergyProfile_eq_one (by omega)

/-- The ordered `l1` distance is exactly the positive-mode distance: the
translation coordinate contributes `|0 - 0|`. -/
theorem orderedLowTenthEnergyShape_l1_eq_positive
    {N : Nat} [NeZero N] :
    (∑ mode : Fin N,
      |orderedLowTenthEnergyShape N mode -
        orderedPositiveUniformWeight N mode|) =
      ∑ mode : Fin (N - 1),
        |lowTenthPositiveEnergyProfile (N - 1) mode -
          1 / ((N - 1 : Nat) : Real)| := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  rw [Fin.sum_univ_castSucc]
  have hsum :
      (∑ mode : Fin M,
        |orderedLowTenthEnergyShape M.succ mode.castSucc -
          orderedPositiveUniformWeight M.succ mode.castSucc|) =
        ∑ mode : Fin M,
          |lowTenthPositiveEnergyProfile M mode - 1 / (M : Real)| := by
    apply Finset.sum_congr rfl
    intro mode _hmode
    simp [orderedLowTenthEnergyShape,
      orderedPositiveUniformWeight, mode.isLt]
  rw [hsum]
  simp [orderedLowTenthEnergyShape, orderedPositiveUniformWeight]

/-- Exact finite-volume distance from positive-mode equipartition. -/
theorem orderedLowTenthEnergyShape_l1_eq {N : Nat} [NeZero N]
    (hN : 2 <= N) :
    (∑ mode : Fin N,
      |orderedLowTenthEnergyShape N mode -
        orderedPositiveUniformWeight N mode|) =
      2 * (1 -
        (excitedPositiveModeCount (N - 1) : Real) /
          ((N - 1 : Nat) : Real)) := by
  rw [orderedLowTenthEnergyShape_l1_eq_positive]
  exact lowTenthPositiveEnergyProfile_l1_eq (by omega)

theorem orderedLowTenthEnergyShape_l1_pos {N : Nat} [NeZero N]
    (hN : 3 <= N) :
    0 < ∑ mode : Fin N,
      |orderedLowTenthEnergyShape N mode -
        orderedPositiveUniformWeight N mode| := by
  rw [orderedLowTenthEnergyShape_l1_eq_positive]
  exact lowTenthPositiveEnergyProfile_l1_pos (by omega)

/-! ## The concrete canonical uniform-mass / Haar-phase ensemble -/

/-- Canonical sample space for iid uniform masses and iid Haar phases. -/
abbrev SampleSpace := RandomEnsemble.SampleSpace

/-- Paper-faithful canonical ensemble: iid uniform masses on `[4/5,6/5]`
and an independent iid Haar phase block. -/
def paperUniformEnsemble : IIDMassPhaseEnsemble SampleSpace :=
  canonicalIIDMassPhaseEnsemble

/-- Ordered periodic modes, with the last index reserved for translation. -/
abbrev OrderedMode (N : Nat) [NeZero N] :=
  Fin (Fintype.card (Lattice.Site N))

/-- The concrete paper-numerical periodic energy shape. -/
def orderedEnergyShape (N : Nat) [NeZero N]
    (mode : OrderedMode N) : Real :=
  orderedLowTenthEnergyShape (Fintype.card (Lattice.Site N)) mode

/-- Extensive modal energy at density `energyDensity`. -/
def orderedModalEnergy (N : Nat) [NeZero N] (energyDensity : Real)
    (mode : OrderedMode N) : Real :=
  (N : Real) * energyDensity * orderedEnergyShape N mode

/-- The complete initial phase block. -/
def initialPhase {N : Nat} [NeZero N] (sample : SampleSpace) :
    Lattice.Site N -> UnitAddCircle :=
  paperUniformEnsemble.restrictPhase sample

theorem massCoordinate_hasLaw (index : Nat) :
    HasLaw (paperUniformEnsemble.mass index)
      RandomEnsemble.massCoordinateLaw paperUniformEnsemble.probability :=
  paperUniformEnsemble.mass_hasLaw index

theorem massCoordinate_mem_support (index : Nat) (sample : SampleSpace) :
    paperUniformEnsemble.mass index sample ∈ RandomEnsemble.massSupport :=
  paperUniformEnsemble.mass_mem_support index sample

theorem orderedEnergyShape_nonneg {N : Nat} [NeZero N]
    (mode : OrderedMode N) : 0 <= orderedEnergyShape N mode :=
  orderedLowTenthEnergyShape_nonneg _ mode

theorem sum_orderedEnergyShape_eq_one {N : Nat} [NeZero N]
    (hN : 2 <= N) :
    (∑ mode : OrderedMode N, orderedEnergyShape N mode) = 1 := by
  unfold orderedEnergyShape
  apply sum_orderedLowTenthEnergyShape_eq_one
  simpa [Lattice.Site] using hN

theorem orderedModalEnergy_nonneg {N : Nat} [NeZero N]
    {energyDensity : Real} (henergyDensity : 0 <= energyDensity)
    (mode : OrderedMode N) :
    0 <= orderedModalEnergy N energyDensity mode := by
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg N) henergyDensity)
    (orderedEnergyShape_nonneg mode)

/-- At density `energyDensity`, total prescribed energy is exactly extensive. -/
theorem sum_orderedModalEnergy_eq_total {N : Nat} [NeZero N]
    (hN : 2 <= N) (energyDensity : Real) :
    (∑ mode : OrderedMode N, orderedModalEnergy N energyDensity mode) =
      (N : Real) * energyDensity := by
  simp only [orderedModalEnergy]
  rw [← Finset.mul_sum, sum_orderedEnergyShape_eq_one hN, mul_one]

/-- Exact shape-level distance from positive-mode equipartition. -/
theorem orderedEnergyShape_l1_eq {N : Nat} [NeZero N]
    (hN : 2 <= N) :
    (∑ mode : OrderedMode N,
      |orderedEnergyShape N mode -
        orderedPositiveUniformWeight
          (Fintype.card (Lattice.Site N)) mode|) =
      2 * (1 -
        (excitedPositiveModeCount (N - 1) : Real) /
          ((N - 1 : Nat) : Real)) := by
  simpa [orderedEnergyShape, Lattice.Site] using
    (orderedLowTenthEnergyShape_l1_eq
      (N := Fintype.card (Lattice.Site N))
      (by simpa [Lattice.Site] using hN))

/-- For `N >= 3` the profile is rigorously nonequilibrium. -/
theorem orderedEnergyShape_l1_pos {N : Nat} [NeZero N]
    (hN : 3 <= N) :
    0 < ∑ mode : OrderedMode N,
      |orderedEnergyShape N mode -
        orderedPositiveUniformWeight
          (Fintype.card (Lattice.Site N)) mode| := by
  simpa [orderedEnergyShape, Lattice.Site] using
    (orderedLowTenthEnergyShape_l1_pos
      (N := Fintype.card (Lattice.Site N))
      (by simpa [Lattice.Site] using hN))

/-- The complete finite phase block has normalized product Haar law, hence
its coordinates are iid Haar. -/
theorem initialPhase_hasLaw {N : Nat} [NeZero N] :
    HasLaw (initialPhase (N := N))
      (finitePhaseHaarLaw (Lattice.Site N))
      paperUniformEnsemble.probability := by
  change HasLaw (paperUniformEnsemble.restrictPhase (N := N))
    (finitePhaseHaarLaw (Lattice.Site N)) paperUniformEnsemble.probability
  exact restrictPhase_hasLaw_finitePhaseHaarLaw paperUniformEnsemble

/-- The finite mass block and full initial phase block are independent. -/
theorem initialMass_indep_initialPhase {N : Nat} [NeZero N] :
    IndepFun (paperUniformEnsemble.restrictMass (N := N))
      (initialPhase (N := N)) paperUniformEnsemble.probability := by
  change IndepFun (paperUniformEnsemble.restrictMass (N := N))
    (paperUniformEnsemble.restrictPhase (N := N))
    paperUniformEnsemble.probability
  exact paperUniformEnsemble.restrictMass_indep_restrictPhase

end

end ArchonPhysics.PaperNumericalLowTenthInitialEnsemble
