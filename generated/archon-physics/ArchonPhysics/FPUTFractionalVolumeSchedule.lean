import ArchonPhysics.EqualMassPeriodicFPUTAlphaNTJointRemainder
import ArchonPhysics.FPUTFiniteTimeCollisionBVQuadrature

/-!
# Fractional power schedules for the FPUT kinetic window

The integer-power schedules used for some finite-volume remainder estimates
cannot express a genuinely mesoscopic time window: no natural exponent is
strictly between zero and one.  This module uses real powers instead.  For
the canonical positive volume `V_n = n + 1`, it sets

* `T_n = V_n ^ b`, and
* `alpha_n = V_n ^ (-a)`.

It proves the exact open window `0 < b < 1`, the general power-counting rule
`b q + d < a p`, and feeds this schedule into the unconditional bounded-
variation collision-grid diagonal.
-/

namespace ArchonPhysics.FPUTFractionalVolumeSchedule

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTAlphaNTJointRemainder
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalPositiveRootBrillouin
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalUmklappCompactTest
open ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate
open ArchonPhysics.EqualMassPeriodicFPUTLocalCollisionGridDiagonal
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.FPUTFiniteTimeCollisionBVQuadrature
open Filter Topology

noncomputable section

/-- Fractional weak-coupling schedule `alpha_n = (n+1)^(-a)`. -/
def fractionalInverseVolumePowerCoupling (a : Real) (n : Nat) : Real :=
  Real.rpow (volumeScale n) (-a)

/-- Fractional mesoscopic time schedule `T_n = (n+1)^b`. -/
def fractionalVolumePowerTime (b : Real) (n : Nat) : Real :=
  Real.rpow (volumeScale n) b

theorem fractionalInverseVolumePowerCoupling_pos
    (a : Real) (n : Nat) :
    0 < fractionalInverseVolumePowerCoupling a n := by
  exact Real.rpow_pos_of_pos (volumeScale_pos n) (-a)

theorem fractionalVolumePowerTime_pos (b : Real) (n : Nat) :
    0 < fractionalVolumePowerTime b n := by
  exact Real.rpow_pos_of_pos (volumeScale_pos n) b

/-- Every positive fractional exponent produces a diverging time window. -/
theorem fractionalVolumePowerTime_tendsto_atTop
    {b : Real} (hb : 0 < b) :
    Tendsto (fractionalVolumePowerTime b) atTop atTop := by
  exact (tendsto_rpow_atTop hb).comp volumeScale_tendsto_atTop

/-- Every sublinear fractional exponent gives the optimal `T_n / V_n -> 0`
collision-grid window. -/
theorem fractionalVolumePowerTime_div_volume_tendsto_zero
    {b : Real} (hb : b < 1) :
    Tendsto
      (fun n : Nat => fractionalVolumePowerTime b n / volumeScale n)
      atTop (nhds 0) := by
  have hlimit :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hb)).comp
      volumeScale_tendsto_atTop
  convert hlimit using 1
  funext n
  have hV : 0 < volumeScale n := volumeScale_pos n
  change Real.rpow (volumeScale n) b / volumeScale n =
    Real.rpow (volumeScale n) (-(1 - b))
  calc
    Real.rpow (volumeScale n) b / volumeScale n =
        Real.rpow (volumeScale n) b /
          Real.rpow (volumeScale n) 1 := by
      congr 1
      exact (Real.rpow_one (volumeScale n)).symm
    _ = Real.rpow (volumeScale n) (b - 1) :=
      (Real.rpow_sub hV b 1).symm
    _ = Real.rpow (volumeScale n) (-(1 - b)) := by
      congr 1
      ring

/-- A scheduled power-counting monomial.  The last factor is a possible
positive volume loss from mode counting or a norm conversion. -/
def fractionalScheduleMonomial
    (a b : Real) (p q d : Nat) (n : Nat) : Real :=
  |fractionalInverseVolumePowerCoupling a n| ^ p *
    |fractionalVolumePowerTime b n| ^ q * volumeScale n ^ d

theorem fractionalScheduleMonomial_eq_rpow
    (a b : Real) (p q d : Nat) (n : Nat) :
    fractionalScheduleMonomial a b p q d n =
      Real.rpow (volumeScale n)
        (-a * (p : Real) + b * (q : Real) + (d : Real)) := by
  have hV : 0 < volumeScale n := volumeScale_pos n
  rw [fractionalScheduleMonomial,
    abs_of_pos (fractionalInverseVolumePowerCoupling_pos a n),
    abs_of_pos (fractionalVolumePowerTime_pos b n)]
  change
    (Real.rpow (volumeScale n) (-a)) ^ p *
        (Real.rpow (volumeScale n) b) ^ q * volumeScale n ^ d = _
  have hp : (Real.rpow (volumeScale n) (-a)) ^ p =
      Real.rpow (volumeScale n) (-a * (p : Real)) :=
    (Real.rpow_mul_natCast hV.le (-a) p).symm
  have hq : (Real.rpow (volumeScale n) b) ^ q =
      Real.rpow (volumeScale n) (b * (q : Real)) :=
    (Real.rpow_mul_natCast hV.le b q).symm
  have hd : volumeScale n ^ d =
      Real.rpow (volumeScale n) (d : Real) :=
    (Real.rpow_natCast (volumeScale n) d).symm
  rw [hp, hq, hd]
  calc
    Real.rpow (volumeScale n) (-a * (p : Real)) *
          Real.rpow (volumeScale n) (b * (q : Real)) *
          Real.rpow (volumeScale n) (d : Real) =
        Real.rpow (volumeScale n)
            (-a * (p : Real) + b * (q : Real)) *
          Real.rpow (volumeScale n) (d : Real) := by
      exact congrArg
        (fun x : Real ↦ x * Real.rpow (volumeScale n) (d : Real))
        (Real.rpow_add hV
          (-a * (p : Real)) (b * (q : Real))).symm
    _ = Real.rpow (volumeScale n)
        (-a * (p : Real) + b * (q : Real) + (d : Real)) :=
      (Real.rpow_add hV
        (-a * (p : Real) + b * (q : Real)) (d : Real)).symm

/-- General fractional power-counting engine.  A factor
`|alpha_n|^p |T_n|^q V_n^d` vanishes whenever its net real exponent is
strictly negative, i.e. `b q + d < a p`. -/
theorem fractionalScheduleMonomial_tendsto_zero
    {a b : Real} {p q d : Nat}
    (hexponent : b * (q : Real) + (d : Real) < a * (p : Real)) :
    Tendsto (fractionalScheduleMonomial a b p q d) atTop (nhds 0) := by
  let gap : Real := a * (p : Real) - (b * (q : Real) + (d : Real))
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hlimit :=
    (tendsto_rpow_neg_atTop hgap).comp volumeScale_tendsto_atTop
  convert hlimit using 1
  funext n
  rw [fractionalScheduleMonomial_eq_rpow]
  congr 1
  dsimp [gap]
  ring

/-- The real-power mesoscopic schedule closes the actual rooted local
collision diagonal for every `0 < b < 1`. -/
theorem actualRootedLocalFourierGridCollision_tendsto_rate_fractionalSchedule
    {N0 : Nat} [NeZero N0] (alpha : Real)
    (out : ActualInteractionBranchMode N0)
    (diagram : ActiveFeedbackEffectiveDiagramImage N0 out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
    (ha0 : 0 ≤ canonicalDiagramLocalLeft diagram)
    (hb2pi : canonicalDiagramLocalRight diagram ≤ 2 * Real.pi)
    {b : Real} (hb0 : 0 < b) (hb1 : b < 1) :
    Tendsto
      (fun n : Nat ↦
        localFourierGridCollisionQuadrature (n + 1)
          (canonicalDiagramUmklappMismatch diagram)
          (actualRootedLocalCollisionMark alpha out diagram)
          (canonicalDiagramLocalLeft diagram)
          (canonicalDiagramLocalRight diagram)
          (canonicalPositiveGeometry_principalZone
            (canonicalDiagramGridK₀_pos diagram)
            (canonicalDiagramGridK₀_lt_two_pi diagram)
            (canonicalDiagramGridK₁_pos diagram)
            (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc).interval_lt.le
          (fractionalVolumePowerTime b n))
      atTop (nhds (actualRootedLocalCollisionRate alpha out diagram)) := by
  apply
    actualRootedLocalFourierGridCollision_tendsto_rate_of_linearTime_unconditional
      alpha out diagram hdisc ha0 hb2pi
      (fractionalVolumePowerTime b)
  · exact fractionalVolumePowerTime_pos b
  · exact fractionalVolumePowerTime_tendsto_atTop hb0
  · simpa only [volumeScale] using
      fractionalVolumePowerTime_div_volume_tendsto_zero hb1

/-- The canonical nonempty witness `b = 1/2`. -/
theorem halfPowerTime_tendsto_atTop :
    Tendsto (fractionalVolumePowerTime (1 / 2 : Real)) atTop atTop := by
  apply fractionalVolumePowerTime_tendsto_atTop
  norm_num

theorem halfPowerTime_div_volume_tendsto_zero :
    Tendsto
      (fun n : Nat ↦
        fractionalVolumePowerTime (1 / 2 : Real) n / volumeScale n)
      atTop (nhds 0) := by
  apply fractionalVolumePowerTime_div_volume_tendsto_zero
  norm_num

end

end ArchonPhysics.FPUTFractionalVolumeSchedule
