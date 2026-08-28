import ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate
import ArchonPhysics.EqualMassPeriodicFPUTPeriodicContinuumMismatch
import ArchonPhysics.ResonanceWeightSinc

/-!
# Near-resonant Fourier-grid certificate for the canonical Umklapp root

The canonical positive Umklapp root is approximated from below by an explicit
periodic Fourier-grid mode.  The angular error is less than one grid spacing
and the Umklapp energy mismatch is therefore `O(1/N)`.  A joint window
`T_N/N → 0` makes the associated rescaled sinc argument vanish.

These are local near-resonance statements, not a Riemann-sum or kinetic-limit
theorem.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTNearResonantGridCertificate

open Set
open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalPositiveRootBrillouin
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTDirectSectorClosure
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate
open ArchonPhysics.EqualMassPeriodicFPUTPeriodicContinuumMismatch
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionChartAdapter
open ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.Lattice
open ArchonPhysics.NormalizedResonancePeakKernel
open Filter MeasureTheory Topology

noncomputable section

/-! ## An explicit one-sided Fourier-grid approximant -/

def lowerFourierGridScaledCoordinate (N : Nat) (x : Real) : Real :=
  (N : Real) * x / (2 * Real.pi)

def lowerFourierGridIndex (N : Nat) (x : Real) : Nat :=
  ⌊lowerFourierGridScaledCoordinate N x⌋₊

def lowerFourierGridMode (N : Nat) [NeZero N] (x : Real) : Site N :=
  (lowerFourierGridIndex N x : ZMod N)

theorem lowerFourierGridIndex_lt_volume
    (N : Nat) [NeZero N] {x : Real}
    (hx0 : 0 ≤ x) (hx2pi : x < 2 * Real.pi) :
    lowerFourierGridIndex N x < N := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have htwoPi : 0 < 2 * Real.pi := by positivity
  have hscaled0 : 0 ≤ lowerFourierGridScaledCoordinate N x := by
    unfold lowerFourierGridScaledCoordinate
    positivity
  have hfloor : (lowerFourierGridIndex N x : Real) ≤
      lowerFourierGridScaledCoordinate N x := by
    exact Nat.floor_le hscaled0
  have hscaledN : lowerFourierGridScaledCoordinate N x < (N : Real) := by
    unfold lowerFourierGridScaledCoordinate
    rw [div_lt_iff₀ htwoPi]
    nlinarith [mul_lt_mul_of_pos_left hx2pi hN]
  exact_mod_cast hfloor.trans_lt hscaledN

theorem lowerFourierGridMode_val
    (N : Nat) [NeZero N] {x : Real}
    (hx0 : 0 ≤ x) (hx2pi : x < 2 * Real.pi) :
    (lowerFourierGridMode N x).val = lowerFourierGridIndex N x := by
  exact ZMod.val_natCast_of_lt
    (lowerFourierGridIndex_lt_volume N hx0 hx2pi)

/-- The lower grid representative is below `x` and misses it by strictly
less than one grid spacing. -/
theorem lowerFourierGridMode_error
    (N : Nat) [NeZero N] {x : Real}
    (hx0 : 0 ≤ x) (hx2pi : x < 2 * Real.pi) :
    0 ≤ x - gridWaveNumber N (lowerFourierGridMode N x) ∧
      x - gridWaveNumber N (lowerFourierGridMode N x) <
        2 * Real.pi / (N : Real) := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hspacing : 0 < 2 * Real.pi / (N : Real) := by positivity
  have hscaled0 : 0 ≤ lowerFourierGridScaledCoordinate N x := by
    unfold lowerFourierGridScaledCoordinate
    positivity
  have hfloor : (lowerFourierGridIndex N x : Real) ≤
      lowerFourierGridScaledCoordinate N x :=
    Nat.floor_le hscaled0
  have hnext : lowerFourierGridScaledCoordinate N x <
      (lowerFourierGridIndex N x : Real) + 1 :=
    Nat.lt_floor_add_one _
  have hlower := mul_le_mul_of_nonneg_left hfloor hspacing.le
  have hupper := mul_lt_mul_of_pos_left hnext hspacing
  have hscaledIdentity :
      (2 * Real.pi / (N : Real)) *
          lowerFourierGridScaledCoordinate N x = x := by
    unfold lowerFourierGridScaledCoordinate
    field_simp [ne_of_gt hN]
  have hgridIdentity :
      gridWaveNumber N (lowerFourierGridMode N x) =
        (2 * Real.pi / (N : Real)) *
          (lowerFourierGridIndex N x : Real) := by
    unfold gridWaveNumber
    rw [lowerFourierGridMode_val N hx0 hx2pi]
    ring
  rw [hscaledIdentity] at hlower hupper
  rw [hgridIdentity]
  constructor
  · linarith
  · linarith

theorem abs_lowerFourierGridMode_sub_lt
    (N : Nat) [NeZero N] {x : Real}
    (hx0 : 0 ≤ x) (hx2pi : x < 2 * Real.pi) :
    |gridWaveNumber N (lowerFourierGridMode N x) - x| <
      2 * Real.pi / (N : Real) := by
  have herror := lowerFourierGridMode_error N hx0 hx2pi
  rw [abs_of_nonpos (by linarith [herror.1])]
  linarith [herror.2]

/-! ## The canonical root and its `O(1/N)` mismatch -/

def canonicalPositiveRootGridMode
    (N : Nat) [NeZero N] (k₀ k₁ : Real) : Site N :=
  lowerFourierGridMode N
    (umklappArcsineRoot (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁)

theorem canonicalPositiveRootGridMode_error
    (N : Nat) [NeZero N] {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    |gridWaveNumber N (canonicalPositiveRootGridMode N k₀ k₁) -
        umklappArcsineRoot
          (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁| <
      2 * Real.pi / (N : Real) :=
  abs_lowerFourierGridMode_sub_lt N
    (canonicalPositiveArcsineRoot_pos
      hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc).le
    (canonicalPositiveArcsineRoot_lt_two_pi
      hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc)

theorem abs_continuumAcousticFrequency_sub_le (x y : Real) :
    |continuumAcousticFrequency x - continuumAcousticFrequency y| ≤
      |x - y| := by
  unfold continuumAcousticFrequency
  calc
    |2 * Real.sin (x / 2) - 2 * Real.sin (y / 2)| =
        2 * |Real.sin (x / 2) - Real.sin (y / 2)| := by
      rw [← mul_sub, abs_mul]
      norm_num
    _ ≤ 2 * |x / 2 - y / 2| :=
      mul_le_mul_of_nonneg_left
        (Real.abs_sin_sub_sin_le (x / 2) (y / 2)) (by norm_num)
    _ = |x - y| := by
      rw [← sub_div, abs_div]
      norm_num
      ring

theorem abs_umklappReducedFourWaveMismatch_sub_le
    (k₀ k₁ x y : Real) :
    |umklappReducedFourWaveMismatch k₀ k₁ x -
        umklappReducedFourWaveMismatch k₀ k₁ y| ≤
      2 * |x - y| := by
  have hx := abs_continuumAcousticFrequency_sub_le y x
  have hraw := abs_continuumAcousticFrequency_sub_le
    (k₀ + k₁ - x) (k₀ + k₁ - y)
  unfold umklappReducedFourWaveMismatch
  calc
    |continuumAcousticFrequency k₀ + continuumAcousticFrequency k₁ -
          continuumAcousticFrequency x +
          continuumAcousticFrequency (k₀ + k₁ - x) -
        (continuumAcousticFrequency k₀ + continuumAcousticFrequency k₁ -
          continuumAcousticFrequency y +
          continuumAcousticFrequency (k₀ + k₁ - y))| =
        |(continuumAcousticFrequency y - continuumAcousticFrequency x) +
          (continuumAcousticFrequency (k₀ + k₁ - x) -
            continuumAcousticFrequency (k₀ + k₁ - y))| := by
      congr 1
      ring
    _ ≤ |continuumAcousticFrequency y - continuumAcousticFrequency x| +
        |continuumAcousticFrequency (k₀ + k₁ - x) -
          continuumAcousticFrequency (k₀ + k₁ - y)| :=
      abs_add_le _ _
    _ ≤ |y - x| +
        |(k₀ + k₁ - x) - (k₀ + k₁ - y)| :=
      add_le_add hx hraw
    _ = 2 * |x - y| := by
      rw [abs_sub_comm y x]
      have : (k₀ + k₁ - x) - (k₀ + k₁ - y) = y - x := by ring
      rw [this, abs_sub_comm y x]
      ring

theorem canonicalPositiveRootGridMode_mismatch_abs_lt
    (N : Nat) [NeZero N] {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    |umklappReducedFourWaveMismatch k₀ k₁
        (gridWaveNumber N (canonicalPositiveRootGridMode N k₀ k₁))| <
      4 * Real.pi / (N : Real) := by
  let root := umklappArcsineRoot
    (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁
  have hroot : umklappReducedFourWaveMismatch k₀ k₁ root = 0 :=
    umklappArcsineRoot_resonant hdisc _
  have hlipschitz := abs_umklappReducedFourWaveMismatch_sub_le
    k₀ k₁ (gridWaveNumber N
      (canonicalPositiveRootGridMode N k₀ k₁)) root
  rw [hroot, sub_zero] at hlipschitz
  have hgrid := canonicalPositiveRootGridMode_error
    N hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc
  calc
    |umklappReducedFourWaveMismatch k₀ k₁
        (gridWaveNumber N (canonicalPositiveRootGridMode N k₀ k₁))| ≤
        2 * |gridWaveNumber N (canonicalPositiveRootGridMode N k₀ k₁) -
          root| := hlipschitz
    _ < 2 * (2 * Real.pi / (N : Real)) :=
      mul_lt_mul_of_pos_left hgrid (by norm_num)
    _ = 4 * Real.pi / (N : Real) := by ring

/-! ## Certificate replacing exact root alignment by an explicit grid mode -/

structure NearResonantExplicitCollisionKernelCertificate
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) : Prop where
  coupling_ne_zero : alpha ≠ 0
  twoToTwo_sector :
    IsExternalTwoToTwoSignSector (reachableEffectiveDiagram diagram)
  transverse : 0 < umklappTransverseDiscriminant
    (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)
  free_mode_is_root_grid :
    canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 2 =
      canonicalPositiveRootGridMode N
        (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)
  umklapp_grid_branch :
    reducedTwoToTwoMismatch
        (outputMomentum (reachableEffectiveDiagram diagram))
        (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 1)
        (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 2) =
      umklappReducedFourWaveMismatch
        (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)
        (canonicalDiagramGridK₂ diagram)

theorem NearResonantExplicitCollisionKernelCertificate.gridK₂_eq_rootGrid
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : NearResonantExplicitCollisionKernelCertificate
      alpha out diagram) :
    canonicalDiagramGridK₂ diagram =
      gridWaveNumber N (canonicalPositiveRootGridMode N
        (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) := by
  unfold canonicalDiagramGridK₂
  rw [certificate.free_mode_is_root_grid]

theorem NearResonantExplicitCollisionKernelCertificate.root_error
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : NearResonantExplicitCollisionKernelCertificate
      alpha out diagram) :
    |canonicalDiagramGridK₂ diagram -
        umklappArcsineRoot
          (umklappPositiveArcsineBranch
            (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
          (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)| <
      2 * Real.pi / (N : Real) := by
  rw [certificate.gridK₂_eq_rootGrid]
  exact canonicalPositiveRootGridMode_error N
    (canonicalDiagramGridK₀_pos diagram)
    (canonicalDiagramGridK₀_lt_two_pi diagram)
    (canonicalDiagramGridK₁_pos diagram)
    (canonicalDiagramGridK₁_lt_two_pi diagram)
    certificate.transverse

theorem NearResonantExplicitCollisionKernelCertificate.discreteMismatch_abs_lt
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : NearResonantExplicitCollisionKernelCertificate
      alpha out diagram) :
    |reducedTwoToTwoMismatch
        (outputMomentum (reachableEffectiveDiagram diagram))
        (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 1)
        (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 2)| <
      4 * Real.pi / (N : Real) := by
  rw [certificate.umklapp_grid_branch, certificate.gridK₂_eq_rootGrid]
  exact canonicalPositiveRootGridMode_mismatch_abs_lt N
    (canonicalDiagramGridK₀_pos diagram)
    (canonicalDiagramGridK₀_lt_two_pi diagram)
    (canonicalDiagramGridK₁_pos diagram)
    (canonicalDiagramGridK₁_lt_two_pi diagram)
    certificate.transverse

theorem NearResonantExplicitCollisionKernelCertificate.rate_pos
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : NearResonantExplicitCollisionKernelCertificate
      alpha out diagram) :
    0 < actualRootedLocalCollisionRate alpha out diagram :=
  actualRootedLocalCollisionRate_pos certificate.coupling_ne_zero
    out diagram certificate.transverse

theorem NearResonantExplicitCollisionKernelCertificate.collision_limit
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : NearResonantExplicitCollisionKernelCertificate
      alpha out diagram) :
    Tendsto
      (fun T : Real ↦ ∫ z in
        umklappArcsineLocalLeft
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)..
          umklappArcsineLocalRight
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram),
        normalizedFiniteTimeResonanceKernel
            (umklappReducedFourWaveMismatch
              (canonicalDiagramGridK₀ diagram)
              (canonicalDiagramGridK₁ diagram) z) T *
          actualRootedLocalCollisionMark alpha out diagram z)
      atTop (nhds (actualRootedLocalCollisionRate alpha out diagram)) :=
  tendsto_actualRootedLocalCollision alpha out diagram certificate.transverse

/-! ## Joint `T_N/N → 0` sinc window -/

theorem canonicalRootGrid_sincArgument_tendsto_zero
    (k₀ k₁ time : Nat → Real)
    (hk₀0 : ∀ n, 0 < k₀ n) (hk₀2pi : ∀ n, k₀ n < 2 * Real.pi)
    (hk₁0 : ∀ n, 0 < k₁ n) (hk₁2pi : ∀ n, k₁ n < 2 * Real.pi)
    (hdisc : ∀ n, 0 < umklappTransverseDiscriminant (k₀ n) (k₁ n))
    (hscale : Tendsto (fun n : Nat ↦ time n / ((n + 1 : Nat) : Real))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        umklappReducedFourWaveMismatch (k₀ n) (k₁ n)
            (gridWaveNumber (n + 1)
              (canonicalPositiveRootGridMode (n + 1) (k₀ n) (k₁ n))) *
          time n / 2)
      atTop (nhds 0) := by
  let argument : Nat → Real := fun n ↦
    umklappReducedFourWaveMismatch (k₀ n) (k₁ n)
        (gridWaveNumber (n + 1)
          (canonicalPositiveRootGridMode (n + 1) (k₀ n) (k₁ n))) *
      time n / 2
  let upper : Nat → Real := fun n ↦
    2 * Real.pi * |time n / ((n + 1 : Nat) : Real)|
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp [upper]
    simpa using tendsto_const_nhds.mul hscale.abs
  have habs : Tendsto (fun n ↦ |argument n|) atTop (nhds 0) := by
    apply squeeze_zero' (g := upper)
    · exact Eventually.of_forall fun _ ↦ abs_nonneg _
    · exact Eventually.of_forall fun n ↦ by
        have hmismatch := canonicalPositiveRootGridMode_mismatch_abs_lt
          (n + 1) (hk₀0 n) (hk₀2pi n) (hk₁0 n) (hk₁2pi n) (hdisc n)
        have hvolume : (0 : Real) < (n : Real) + 1 := by positivity
        dsimp [argument, upper]
        rw [abs_div, abs_mul]
        norm_num
        calc
          |umklappReducedFourWaveMismatch (k₀ n) (k₁ n)
              (gridWaveNumber (n + 1)
                (canonicalPositiveRootGridMode (n + 1) (k₀ n) (k₁ n)))| *
                |time n| / 2 ≤
              (4 * Real.pi / ((n : Real) + 1)) * |time n| / 2 := by
                have hcoeff :
                    |umklappReducedFourWaveMismatch (k₀ n) (k₁ n)
                        (gridWaveNumber (n + 1)
                          (canonicalPositiveRootGridMode
                            (n + 1) (k₀ n) (k₁ n)))| ≤
                      4 * Real.pi / ((n : Real) + 1) := by
                  simpa [Nat.cast_add, Nat.cast_one] using hmismatch.le
                gcongr
          _ = 2 * Real.pi * |time n / ((n : Real) + 1)| := by
            rw [abs_div, abs_of_pos hvolume]
            ring
    · exact hupper
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs, argument] using habs

theorem canonicalRootGrid_sincSquare_tendsto_one
    (k₀ k₁ time : Nat → Real)
    (hk₀0 : ∀ n, 0 < k₀ n) (hk₀2pi : ∀ n, k₀ n < 2 * Real.pi)
    (hk₁0 : ∀ n, 0 < k₁ n) (hk₁2pi : ∀ n, k₁ n < 2 * Real.pi)
    (hdisc : ∀ n, 0 < umklappTransverseDiscriminant (k₀ n) (k₁ n))
    (hscale : Tendsto (fun n : Nat ↦ time n / ((n + 1 : Nat) : Real))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        Real.sinc
          (umklappReducedFourWaveMismatch (k₀ n) (k₁ n)
              (gridWaveNumber (n + 1)
                (canonicalPositiveRootGridMode (n + 1) (k₀ n) (k₁ n))) *
            time n / 2) ^ 2)
      atTop (nhds 1) := by
  have hargument := canonicalRootGrid_sincArgument_tendsto_zero
    k₀ k₁ time hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc hscale
  have hsinc := Real.continuous_sinc.continuousAt.tendsto.comp hargument
  simpa using hsinc.pow 2

end

end ArchonPhysics.EqualMassPeriodicFPUTNearResonantGridCertificate
