import ArchonPhysics.CanonicalIIDCoerciveSourceSlotCouplingScaling

/-!
# Coupling scaling through canonical iid expectations

The pointwise quadratic and quartic source powers proved in the preceding
module are pulled through the Bochner expectation and through both left and
right factorization defects.  The unit defects below use the same actual
alpha--beta trajectory; only the displayed source insertion is normalized.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveSourceSlotCouplingScalingExpectation

open scoped BigOperators Matrix Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotExpectation
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotCouplingScaling
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem canonicalLeftPotentialSourceSlotFactorizationDefect_const_mul
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (unitKappa unitBeta unitG : Real) (c : Complex)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hsource : forall block slot st,
      canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
            sourceKappa sourceBeta sourceG entry block slot st =
        c * canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
            unitKappa unitBeta unitG entry block slot st)
    (left right : Finset I) (slot : I) (time : Real) :
    canonicalLeftPotentialSourceSlotFactorizationDefect (N := N)
        flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry left right slot time =
      c * canonicalLeftPotentialSourceSlotFactorizationDefect (N := N)
        flowKappa flowBeta flowG hflowBeta a
          unitKappa unitBeta unitG entry left right slot time := by
  unfold canonicalLeftPotentialSourceSlotFactorizationDefect
    canonicalPotentialSourceSlotBochnerIntegral
  rw [show (fun omega =>
      canonicalPotentialSourceSlotObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a
              sourceKappa sourceBeta sourceG entry left slot (omega, time) *
          canonicalSignedBlockObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a
              entry right (omega, time)) =
      (fun omega => c *
        (canonicalPotentialSourceSlotObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a
                unitKappa unitBeta unitG entry left slot (omega, time) *
            canonicalSignedBlockObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a
                entry right (omega, time))) by
    funext omega
    rw [hsource]
    ring]
  rw [integral_const_mul]
  rw [show (fun omega =>
      canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry left slot (omega, time)) =
      (fun omega => c * canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
          unitKappa unitBeta unitG entry left slot (omega, time)) by
    funext omega
    exact hsource left slot (omega, time)]
  rw [integral_const_mul]
  ring

theorem canonicalRightPotentialSourceSlotFactorizationDefect_const_mul
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (unitKappa unitBeta unitG : Real) (c : Complex)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hsource : forall block slot st,
      canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
            sourceKappa sourceBeta sourceG entry block slot st =
        c * canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
            unitKappa unitBeta unitG entry block slot st)
    (left right : Finset I) (slot : I) (time : Real) :
    canonicalRightPotentialSourceSlotFactorizationDefect (N := N)
        flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry left right slot time =
      c * canonicalRightPotentialSourceSlotFactorizationDefect (N := N)
        flowKappa flowBeta flowG hflowBeta a
          unitKappa unitBeta unitG entry left right slot time := by
  unfold canonicalRightPotentialSourceSlotFactorizationDefect
    canonicalPotentialSourceSlotBochnerIntegral
  rw [show (fun omega =>
      canonicalSignedBlockObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a
              entry left (omega, time) *
          canonicalPotentialSourceSlotObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a
              sourceKappa sourceBeta sourceG entry right slot (omega, time)) =
      (fun omega => c *
        (canonicalSignedBlockObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a
                entry left (omega, time) *
            canonicalPotentialSourceSlotObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a
                unitKappa unitBeta unitG entry right slot (omega, time))) by
    funext omega
    rw [hsource]
    ring]
  rw [integral_const_mul]
  rw [show (fun omega =>
      canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry right slot (omega, time)) =
      (fun omega => c * canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
          unitKappa unitBeta unitG entry right slot (omega, time)) by
    funext omega
    exact hsource right slot (omega, time)]
  rw [integral_const_mul]
  ring

/-- Unit quadratic left-slot defect on the same actual alpha--beta flow. -/
def canonicalLeftUnitQuadraticSourceSlotFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  canonicalLeftPotentialSourceSlotFactorizationDefect (N := N)
    kappa beta g hbeta a 1 0 1 entry left right slot time

/-- Unit quartic left-slot defect on the same actual alpha--beta flow. -/
def canonicalLeftUnitQuarticSourceSlotFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  canonicalLeftPotentialSourceSlotFactorizationDefect (N := N)
    kappa beta g hbeta a 0 1 1 entry left right slot time

/-- Unit quadratic right-slot defect on the same actual alpha--beta flow. -/
def canonicalRightUnitQuadraticSourceSlotFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  canonicalRightPotentialSourceSlotFactorizationDefect (N := N)
    kappa beta g hbeta a 1 0 1 entry left right slot time

/-- Unit quartic right-slot defect on the same actual alpha--beta flow. -/
def canonicalRightUnitQuarticSourceSlotFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  canonicalRightPotentialSourceSlotFactorizationDefect (N := N)
    kappa beta g hbeta a 0 1 1 entry left right slot time

theorem canonicalLeftQuadraticSourceSlotFactorizationDefect_eq_coupling_mul_unit
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) :
    canonicalLeftQuadraticSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time =
      ((kappa * g : Real) : Complex) *
        canonicalLeftUnitQuadraticSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time := by
  apply canonicalLeftPotentialSourceSlotFactorizationDefect_const_mul
  intro block sourceSlot st
  exact canonicalPotentialSourceSlotObservable_quadratic_eq_coupling_mul_unit
    kappa beta g hbeta a kappa g entry block sourceSlot st

theorem canonicalLeftQuarticSourceSlotFactorizationDefect_eq_coupling_mul_unit
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) :
    canonicalLeftQuarticSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time =
      ((beta * g ^ 2 : Real) : Complex) *
        canonicalLeftUnitQuarticSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time := by
  apply canonicalLeftPotentialSourceSlotFactorizationDefect_const_mul
  intro block sourceSlot st
  exact canonicalPotentialSourceSlotObservable_quartic_eq_coupling_mul_unit
    kappa beta g hbeta a beta g entry block sourceSlot st

theorem canonicalRightQuadraticSourceSlotFactorizationDefect_eq_coupling_mul_unit
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) :
    canonicalRightQuadraticSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time =
      ((kappa * g : Real) : Complex) *
        canonicalRightUnitQuadraticSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time := by
  apply canonicalRightPotentialSourceSlotFactorizationDefect_const_mul
  intro block sourceSlot st
  exact canonicalPotentialSourceSlotObservable_quadratic_eq_coupling_mul_unit
    kappa beta g hbeta a kappa g entry block sourceSlot st

theorem canonicalRightQuarticSourceSlotFactorizationDefect_eq_coupling_mul_unit
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) :
    canonicalRightQuarticSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time =
      ((beta * g ^ 2 : Real) : Complex) *
        canonicalRightUnitQuarticSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time := by
  apply canonicalRightPotentialSourceSlotFactorizationDefect_const_mul
  intro block sourceSlot st
  exact canonicalPotentialSourceSlotObservable_quartic_eq_coupling_mul_unit
    kappa beta g hbeta a beta g entry block sourceSlot st

end

end ArchonPhysics.CanonicalIIDCoerciveSourceSlotCouplingScalingExpectation
