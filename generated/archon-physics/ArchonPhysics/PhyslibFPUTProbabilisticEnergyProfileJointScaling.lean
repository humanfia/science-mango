import ArchonPhysics.PhyslibFPUTProbabilisticFullStateEnergyProfileAdapter

/-!
# Joint mode-count, block-count, and coupling scaling

The all-mode probabilistic full-state adapter gives the finite union bound

`P(jointBad) <= modeCount * K * Cfailure * |g|^3`.

This module isolates the exact numerical conditions under which that bound is
small when lattice size, kinetic block count, and weak coupling vary together.
There are two useful forms:

* without a kinetic-time relation, one assumes directly that
  `modeCount_n * K_n * Cfailure * |g_n|^3 -> 0`;
* under `g_n^2 T K_n <= tau`, it is enough that
  `modeCount_n * |g_n| -> 0`.

Thus an inverse-square time window permits the number of positive modes to
grow only subject to the displayed small-parameter condition.  No
`N`-uniformity, mode-count bound, or automatic relation between lattice size
and coupling is asserted.
-/

namespace ArchonPhysics.PhyslibFPUTProbabilisticEnergyProfileJointScaling

open Filter
open Topology
open MeasureTheory
open ArchonPhysics
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.PhyslibFPUTProbabilisticFullStateEnergyProfileAdapter

noncomputable section

/-! ## Abstract numerical scaling certificate -/

/-- The numerical output of an all-mode/block union bound.  `modeCount` may
vary with `n`, so this structure can represent a genuine joint lattice-size
and weak-coupling limit without pretending that dependent finite-volume state
spaces are definitionally identical. -/
structure JointModeBlockFailureScalingCertificate
    (badProbability : Nat → Real)
    (modeCount blockCount : Nat → Nat)
    (g : Nat → Real) (Cfailure : Real) where
  Cfailure_nonneg : 0 ≤ Cfailure
  badProbability_nonneg : ∀ n, 0 ≤ badProbability n
  badProbability_le : ∀ n,
    badProbability n ≤
      (modeCount n : Real) * (blockCount n : Real) *
        Cfailure * |g n| ^ 3

namespace JointModeBlockFailureScalingCertificate

variable {badProbability : Nat → Real}
  {modeCount blockCount : Nat → Nat}
  {g : Nat → Real} {Cfailure : Real}

/-- A finite-`n` epsilon criterion with every joint scaling factor visible. -/
theorem badProbability_le_epsilon
    (certificate : JointModeBlockFailureScalingCertificate
      badProbability modeCount blockCount g Cfailure)
    (n : Nat) {epsilon : Real}
    (hsmall :
      (modeCount n : Real) * (blockCount n : Real) *
          Cfailure * |g n| ^ 3 ≤ epsilon) :
    badProbability n ≤ epsilon :=
  (certificate.badProbability_le n).trans hsmall

/-- Direct joint-limit criterion, before using any kinetic-time relation. -/
theorem badProbability_tendsto_zero_of_jointScale
    (certificate : JointModeBlockFailureScalingCertificate
      badProbability modeCount blockCount g Cfailure)
    (hscale : Tendsto
      (fun n ↦ (modeCount n : Real) * (blockCount n : Real) *
        Cfailure * |g n| ^ 3) atTop (nhds 0)) :
    Tendsto badProbability atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall certificate.badProbability_nonneg
  · exact Filter.Eventually.of_forall certificate.badProbability_le
  · exact hscale

/-- The inverse-square kinetic budget converts `K |g|^3` into
`(tau / T) |g|`; the growing mode count remains explicit. -/
theorem badProbability_le_kineticTime_modeCoupling
    (certificate : JointModeBlockFailureScalingCertificate
      badProbability modeCount blockCount g Cfailure)
    {T : Real} (hT : 0 < T) (n : Nat) (tau : Real)
    (hkineticBudget :
      (g n ^ 2 * T) * (blockCount n : Real) ≤ tau) :
    badProbability n ≤
      (modeCount n : Real) * (tau / T) * Cfailure * |g n| := by
  have hblockBudget :
      (blockCount n : Real) * |g n| ^ 2 ≤ tau / T := by
    apply (le_div_iff₀ hT).2
    calc
      (blockCount n : Real) * |g n| ^ 2 * T =
          (g n ^ 2 * T) * (blockCount n : Real) := by
        rw [sq_abs]
        ring
      _ ≤ tau := hkineticBudget
  have hscale :
      0 ≤ (modeCount n : Real) * Cfailure * |g n| :=
    mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) certificate.Cfailure_nonneg)
      (abs_nonneg _)
  calc
    badProbability n ≤
        (modeCount n : Real) * (blockCount n : Real) *
          Cfailure * |g n| ^ 3 := certificate.badProbability_le n
    _ = ((blockCount n : Real) * |g n| ^ 2) *
          ((modeCount n : Real) * Cfailure * |g n|) := by ring
    _ ≤ (tau / T) *
          ((modeCount n : Real) * Cfailure * |g n|) :=
      mul_le_mul_of_nonneg_right hblockBudget hscale
    _ = (modeCount n : Real) * (tau / T) * Cfailure * |g n| := by
      ring

/-- Finite-`n` epsilon criterion on a kinetic-time window.  This is the exact
small parameter which must be checked when the number of modes grows. -/
theorem badProbability_le_epsilon_of_kineticBudget
    (certificate : JointModeBlockFailureScalingCertificate
      badProbability modeCount blockCount g Cfailure)
    {T : Real} (hT : 0 < T) (n : Nat) (tau epsilon : Real)
    (hkineticBudget :
      (g n ^ 2 * T) * (blockCount n : Real) ≤ tau)
    (hmodeCouplingSmall :
      (modeCount n : Real) * (tau / T) * Cfailure * |g n| ≤ epsilon) :
    badProbability n ≤ epsilon :=
  (certificate.badProbability_le_kineticTime_modeCoupling
    hT n tau hkineticBudget).trans hmodeCouplingSmall

/-- Joint lattice/weak-coupling limit on a bounded kinetic-time window.
The transparent hypothesis `modeCount_n * |g_n| -> 0` is essential here; it is
not inferred from `g_n -> 0`. -/
theorem badProbability_tendsto_zero_of_kineticBudget
    (certificate : JointModeBlockFailureScalingCertificate
      badProbability modeCount blockCount g Cfailure)
    {T tau : Real} (hT : 0 < T) (_htau : 0 ≤ tau)
    (hkineticBudget : ∀ n,
      (g n ^ 2 * T) * (blockCount n : Real) ≤ tau)
    (hmodeCoupling : Tendsto
      (fun n ↦ (modeCount n : Real) * |g n|) atTop (nhds 0)) :
    Tendsto badProbability atTop (nhds 0) := by
  let scaleConstant := (tau / T) * Cfailure
  have hupper : Tendsto
      (fun n ↦ scaleConstant * ((modeCount n : Real) * |g n|))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hmodeCoupling)
  apply squeeze_zero'
    (g := fun n ↦ scaleConstant * ((modeCount n : Real) * |g n|))
  · exact Filter.Eventually.of_forall certificate.badProbability_nonneg
  · exact Filter.Eventually.of_forall fun n ↦ by
      have hbound := certificate.badProbability_le_kineticTime_modeCoupling
        hT n tau (hkineticBudget n)
      have hreorder :
          (modeCount n : Real) * (tau / T) * Cfailure * |g n| =
            scaleConstant * ((modeCount n : Real) * |g n|) := by
        unfold scaleConstant
        ring
      rwa [hreorder] at hbound
  · exact hupper

end JointModeBlockFailureScalingCertificate

/-! ## Specialization to the probabilistic full-state profile adapter -/

namespace FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter

variable {Omega X : Type*} [MeasurableSpace Omega]
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {mu : Measure Omega} [IsProbabilityMeasure mu] {M : Real}
  {N : Nat} [NeZero N]
  {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
  {g : Nat → Real}
  {E : Nat → Nat → PositiveEnergyProfile m}
  {Cref Ccoupling Cfailure : Real}

/-- Package exactly the all-mode union bound already proved by the adapter as
a numerical scaling certificate.  At fixed `m` its mode count is constant;
joint `N`-limits use the abstract certificate above with a varying
`modeCount`. -/
theorem toJointModeBlockFailureScalingCertificate
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (K : Nat → Nat) :
    JointModeBlockFailureScalingCertificate
      (fun n ↦ mu.real (adapter.firstKAllModesBad n (K n)))
      (fun _ ↦ Fintype.card (PositiveFrequencyMode m)) K g Cfailure where
  Cfailure_nonneg := adapter.Cfailure_nonneg
  badProbability_nonneg := fun _ ↦ measureReal_nonneg
  badProbability_le := fun n ↦
    adapter.firstKAllModesBad_probability_le_abs_cube n (K n)

/-- Finite-`n` all-mode epsilon bound under the raw joint small-parameter
condition. -/
theorem firstKAllModesBad_probability_le_epsilon
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (n K : Nat) (epsilon : Real)
    (hsmall :
      (Fintype.card (PositiveFrequencyMode m) : Real) * (K : Real) *
          Cfailure * |g n| ^ 3 ≤ epsilon) :
    mu.real (adapter.firstKAllModesBad n K) ≤ epsilon :=
  (adapter.firstKAllModesBad_probability_le_abs_cube n K).trans hsmall

/-- Fixed-volume kinetic-window bound.  The positive-mode count remains in
the conclusion so it cannot be mistaken for an `N`-uniform estimate. -/
theorem firstKAllModesBad_probability_le_kineticTime_modeCoupling
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (hT : 0 < T) (n K : Nat) (tau : Real)
    (hkineticBudget : (g n ^ 2 * T) * (K : Real) ≤ tau) :
    mu.real (adapter.firstKAllModesBad n K) ≤
      (Fintype.card (PositiveFrequencyMode m) : Real) *
        (tau / T) * Cfailure * |g n| := by
  let blocks : Nat → Nat := fun _ ↦ K
  have hbound :=
    (toJointModeBlockFailureScalingCertificate adapter blocks)
      |>.badProbability_le_kineticTime_modeCoupling
        hT n tau (by simpa only [blocks] using hkineticBudget)
  simpa only [blocks] using hbound

/-- At fixed finite volume, `g_n -> 0` is enough for the joint bad probability
to vanish on an inverse-square kinetic window.  This theorem is deliberately
separate from the varying-`N` theorem, which needs
`modeCount_n * |g_n| -> 0`. -/
theorem firstKAllModesBad_probability_tendsto_zero_fixedVolume
    (adapter : FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter
      (Omega := Omega) (X := X) mu M m kappa beta T g E
        Cref Ccoupling Cfailure)
    (K : Nat → Nat) {tau : Real} (hT : 0 < T) (htau : 0 ≤ tau)
    (hkineticBudget : ∀ n,
      (g n ^ 2 * T) * (K n : Real) ≤ tau)
    (hg : Tendsto g atTop (nhds 0)) :
    Tendsto (fun n ↦ mu.real (adapter.firstKAllModesBad n (K n)))
      atTop (nhds 0) := by
  have hmodeCoupling : Tendsto
      (fun n ↦ (Fintype.card (PositiveFrequencyMode m) : Real) * |g n|)
      atTop (nhds 0) := by
    have hcard : Tendsto
        (fun _ : Nat ↦ (Fintype.card (PositiveFrequencyMode m) : Real))
        atTop (nhds (Fintype.card (PositiveFrequencyMode m) : Real)) :=
      tendsto_const_nhds
    simpa only [mul_zero, abs_zero] using hcard.mul hg.abs
  exact (toJointModeBlockFailureScalingCertificate adapter K)
    |>.badProbability_tendsto_zero_of_kineticBudget
      hT htau hkineticBudget hmodeCoupling

end FPUTProbabilisticFullStateEnergyProfileBlockwiseAdapter

end


end ArchonPhysics.PhyslibFPUTProbabilisticEnergyProfileJointScaling
