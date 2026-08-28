import ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm

/-!
# Consumer endpoints for the actual periodic alpha-FPUT first normal form

These endpoints expose the exact adapter from a differentiable Physlib
Hamiltonian trajectory to the finite quadratic normal-form API.  They make no
kinetic, random-phase, or volume-uniform assertion.
-/

namespace ArchonPhysicsConsumers.Thermalization

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.EqualMassPeriodicFPUTInteractionPicture
open ArchonPhysics.Lattice
open ArchonPhysics.QuadraticInteractionFirstNormalForm
open Time

noncomputable section

theorem equalMassPeriodicFPUT_actualBranchGlobalGap_consumer
    (N : Nat) [NeZero N]
    (out left right : ActualInteractionBranchMode N) :
    finiteNonzeroMomentumThreeWaveGap N ≤
      |actualQuadraticMismatch N out left right| :=
  finiteGap_le_abs_actualQuadraticMismatch N out left right

theorem equalMassPeriodicFPUT_actualSourceAdapter_consumer
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N) (tau : Real)
    (out : ActualInteractionBranchMode N) :
    quadraticOscillatorySource
        (actualQuadraticVertex N alpha) (actualQuadraticMismatch N)
        (actualInteractionBranchPath p q tau) tau out =
      ∑ l ∈ nonzeroInputMomenta N (actualBranchRawMode out),
        ∑ leftSign ∈ phaseSignFinset,
          ∑ rightSign ∈ phaseSignFinset,
            equalMassQuadraticBranchTerm alpha
              (actualBranchRawMode out) l
              (actualBranchSign out) leftSign rightSign p q tau :=
  quadraticOscillatorySource_actual_eq_explicitBranchSum
    alpha p q tau out

theorem equalMassPeriodicFPUT_actualQuadraticDerivative_consumer
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N)
    (hHamilton :
      SatisfiesHamiltonEquations (unitMassConfig N) 1 0 alpha p q)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    HasDerivAt
      (fun s ↦ actualInteractionBranchPath p q s out)
      ((alpha : Complex) * quadraticOscillatorySource
        (actualQuadraticVertex N 1) (actualQuadraticMismatch N)
        (actualInteractionBranchPath p q tau) tau out) tau :=
  hasDerivAt_actualInteractionBranch_unitVertexSource
    alpha p q hHamilton hp hq tau out

theorem equalMassPeriodicFPUT_actualPrimitiveFixedGap_consumer
    (N : Nat) [NeZero N] (alpha : Real)
    (amplitude : ActualInteractionBranchMode N → Complex)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    ‖(alpha : Complex) * actualFirstNormalFormPrimitive N amplitude tau out‖ ≤
      |alpha| * ((2 / finiteNonzeroMomentumThreeWaveGap N) *
        ∑ left, ∑ right,
          ‖actualQuadraticVertex N 1 out left right‖ *
            ‖amplitude left‖ * ‖amplitude right‖) :=
  norm_alpha_mul_actualFirstNormalFormPrimitive_le_fixedGap
    N alpha amplitude tau out

theorem equalMassPeriodicFPUT_actualFirstNormalForm_consumer
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N)
    (hHamilton :
      SatisfiesHamiltonEquations (unitMassConfig N) 1 0 alpha p q)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (tau : Real) (out : ActualInteractionBranchMode N) :
    HasDerivAt
        (fun s ↦ actualInteractionBranchPath p q s out -
          (alpha : Complex) * actualFirstNormalFormPrimitive N
            (actualInteractionBranchPath p q s) s out)
        (-((alpha : Complex) ^ 2) * actualEffectiveCubicFourWaveSource N
          (actualInteractionBranchPath p q tau) tau out) tau ∧
      ‖(alpha : Complex) * actualFirstNormalFormPrimitive N
          (actualInteractionBranchPath p q tau) tau out‖ ≤
        |alpha| * ((2 / finiteNonzeroMomentumThreeWaveGap N) *
          ∑ left, ∑ right,
            ‖actualQuadraticVertex N 1 out left right‖ *
              ‖actualInteractionBranchPath p q tau left‖ *
              ‖actualInteractionBranchPath p q tau right‖) :=
  actualPhyslib_firstNormalForm
    alpha p q hHamilton hp hq tau out

#print axioms equalMassPeriodicFPUT_actualBranchGlobalGap_consumer
#print axioms equalMassPeriodicFPUT_actualSourceAdapter_consumer
#print axioms equalMassPeriodicFPUT_actualQuadraticDerivative_consumer
#print axioms equalMassPeriodicFPUT_actualPrimitiveFixedGap_consumer
#print axioms equalMassPeriodicFPUT_actualFirstNormalForm_consumer

end

end ArchonPhysicsConsumers.Thermalization
