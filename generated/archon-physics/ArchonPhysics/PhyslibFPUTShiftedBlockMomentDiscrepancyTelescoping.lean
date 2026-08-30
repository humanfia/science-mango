import ArchonPhysics.PhyslibFPUTCoupledRestartKineticResidual

/-!
# Shifted-block moment discrepancies telescope to kinetic-time error

This module is a certificate-free deterministic reduction.  A shifted
reference block has a scalar kinetic residual, while the actual coherent
Hamiltonian moment is close to the reference moment at both endpoints.  The
existing endpoint-transfer theorem first derives the actual residual.  The
existing discrete Gronwall theorem then accumulates those derived residuals.

No actual residual is assumed.  No relation between consecutive reference
blocks is needed: coherence is carried only by the actual endpoint chain.
The generic theorem applies separately to the collision-relevant quadratic
and quartic moments, and the final theorem records both bounds at once.
-/

namespace ArchonPhysics.PhyslibFPUTShiftedBlockMomentDiscrepancyTelescoping

open ArchonPhysics.PhyslibFPUTCoupledRestartKineticResidual
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation

noncomputable section

/-- When the initial and final endpoint discrepancies use the same budget,
the transferred residual is the reference defect plus the discrepancy with
its exact stability multiplier. -/
theorem endpointCoupledKineticResidualDefect_sameEndpointDiscrepancy
    (step L referenceDefect epsilon : Real) :
    endpointCoupledKineticResidualDefect
        step L referenceDefect epsilon epsilon =
      referenceDefect + (2 + step * L) * epsilon := by
  unfold endpointCoupledKineticResidualDefect
  ring

/-- Exact power-weighted telescoping bound for nonuniform shifted-block
endpoint discrepancies.  Every displayed defect is derived from the
reference residual and the two endpoint moment discrepancies. -/
theorem shiftedBlock_endpointMomentDiscrepancy_powerBound
    (actual kinetic referenceInitial referenceFinal : Nat -> Real)
    (Q : Real -> Real) (step L : Real)
    (referenceDefect initialDiscrepancy finalDiscrepancy : Nat -> Real)
    (hstep : 0 <= step) (hL : 0 <= L)
    (hreference : forall j,
      MomentKineticEulerResidual
        (referenceInitial j) (referenceFinal j) step
        (Q (referenceInitial j)) (referenceDefect j))
    (hinitial : forall j,
      |actual j - referenceInitial j| <= initialDiscrepancy j)
    (hfinal : forall j,
      |actual (j + 1) - referenceFinal j| <= finalDiscrepancy j)
    (hkinetic : IsKineticEulerTrajectory kinetic step Q)
    (hQ : forall x y, |Q x - Q y| <= L * |x - y|)
    (K : Nat) :
    |actual K - kinetic K| <=
      |actual 0 - kinetic 0| * (1 + L * step) ^ K +
        ∑ j ∈ Finset.range K,
          endpointCoupledKineticResidualDefect step L
              (referenceDefect j) (initialDiscrepancy j)
              (finalDiscrepancy j) *
            (1 + L * step) ^ (K - (j + 1)) := by
  let defect : Nat -> Real := fun j =>
    endpointCoupledKineticResidualDefect step L
      (referenceDefect j) (initialDiscrepancy j) (finalDiscrepancy j)
  have hactualResidual : forall j,
      MomentKineticEulerResidual
        (actual j) (actual (j + 1)) step (Q (actual j)) (defect j) := by
    intro j
    exact momentKineticEulerResidual_of_reference_endpoint_control
      (actual j) (actual (j + 1))
      (referenceInitial j) (referenceFinal j) Q
      hstep hL (hreference j) (hinitial j) (hfinal j) hQ
  have hrecurrence : forall j,
      |actual (j + 1) - kinetic (j + 1)| <=
        (1 + L * step) * |actual j - kinetic j| + defect j := by
    intro j
    exact abs_microscopic_sub_kinetic_next_le
      actual kinetic Q step L defect hstep hkinetic hactualResidual hQ j
  have hbase := discrete_affine_error_closedForm
    (e := fun j => |actual j - kinetic j|) (defect := defect)
    (L := L) (h := step)
    (add_nonneg zero_le_one (mul_nonneg hL hstep)) hrecurrence K
  simpa only [defect] using hbase

/-- Exponential form with a single discrepancy `epsilon j` controlling both
endpoints of block `j`.  Thus the cumulative price of shifted-block RPA is
the explicit sum

`sum_j (referenceDefect j + (2 + step * L) * epsilon j)`.
-/
theorem shiftedBlock_commonMomentDiscrepancy_expBound
    (actual kinetic referenceInitial referenceFinal : Nat -> Real)
    (Q : Real -> Real) (step L : Real)
    (referenceDefect epsilon : Nat -> Real)
    (hstep : 0 <= step) (hL : 0 <= L)
    (hreferenceDefect : forall j, 0 <= referenceDefect j)
    (hepsilon : forall j, 0 <= epsilon j)
    (hreference : forall j,
      MomentKineticEulerResidual
        (referenceInitial j) (referenceFinal j) step
        (Q (referenceInitial j)) (referenceDefect j))
    (hinitial : forall j,
      |actual j - referenceInitial j| <= epsilon j)
    (hfinal : forall j,
      |actual (j + 1) - referenceFinal j| <= epsilon j)
    (hkinetic : IsKineticEulerTrajectory kinetic step Q)
    (hQ : forall x y, |Q x - Q y| <= L * |x - y|)
    (K : Nat) :
    |actual K - kinetic K| <=
      (|actual 0 - kinetic 0| +
        ∑ j ∈ Finset.range K,
          (referenceDefect j + (2 + step * L) * epsilon j)) *
        Real.exp (L * step * (K : Real)) := by
  let defect : Nat -> Real := fun j =>
    endpointCoupledKineticResidualDefect step L
      (referenceDefect j) (epsilon j) (epsilon j)
  have hdefect : forall j, 0 <= defect j := by
    intro j
    unfold defect endpointCoupledKineticResidualDefect
    exact add_nonneg
      (add_nonneg (hreferenceDefect j) (hepsilon j))
      (mul_nonneg
        (add_nonneg zero_le_one (mul_nonneg hstep hL))
        (hepsilon j))
  have hactualResidual : forall j,
      MomentKineticEulerResidual
        (actual j) (actual (j + 1)) step (Q (actual j)) (defect j) := by
    intro j
    exact momentKineticEulerResidual_of_reference_endpoint_control
      (actual j) (actual (j + 1))
      (referenceInitial j) (referenceFinal j) Q
      hstep hL (hreference j) (hinitial j) (hfinal j) hQ
  have hbase := moment_kineticEuler_shadowing_exp_bound
    actual kinetic Q step L defect hstep hL hdefect
      hkinetic hactualResidual hQ K
  simpa only [defect,
    endpointCoupledKineticResidualDefect_sameEndpointDiscrepancy] using hbase

/-- Simultaneous quadratic/fourth collision-observable specialization.  The
two reference blocks and collision fields may differ, but both are compared
to coherent actual moment chains over the same shifted-block partition. -/
theorem shiftedBlocks_second_fourth_collisionMoment_expBounds
    (actualSecond kineticSecond referenceSecondInitial referenceSecondFinal :
      Nat -> Real)
    (actualFourth kineticFourth referenceFourthInitial referenceFourthFinal :
      Nat -> Real)
    (Qsecond Qfourth : Real -> Real)
    (step Lsecond Lfourth : Real)
    (referenceSecondDefect referenceFourthDefect : Nat -> Real)
    (secondDiscrepancy fourthDiscrepancy : Nat -> Real)
    (hstep : 0 <= step) (hLsecond : 0 <= Lsecond)
    (hLfourth : 0 <= Lfourth)
    (hreferenceSecondDefect : forall j, 0 <= referenceSecondDefect j)
    (hreferenceFourthDefect : forall j, 0 <= referenceFourthDefect j)
    (hsecondDiscrepancy : forall j, 0 <= secondDiscrepancy j)
    (hfourthDiscrepancy : forall j, 0 <= fourthDiscrepancy j)
    (hreferenceSecond : forall j,
      MomentKineticEulerResidual
        (referenceSecondInitial j) (referenceSecondFinal j) step
        (Qsecond (referenceSecondInitial j)) (referenceSecondDefect j))
    (hreferenceFourth : forall j,
      MomentKineticEulerResidual
        (referenceFourthInitial j) (referenceFourthFinal j) step
        (Qfourth (referenceFourthInitial j)) (referenceFourthDefect j))
    (hsecondInitial : forall j,
      |actualSecond j - referenceSecondInitial j| <= secondDiscrepancy j)
    (hsecondFinal : forall j,
      |actualSecond (j + 1) - referenceSecondFinal j| <=
        secondDiscrepancy j)
    (hfourthInitial : forall j,
      |actualFourth j - referenceFourthInitial j| <= fourthDiscrepancy j)
    (hfourthFinal : forall j,
      |actualFourth (j + 1) - referenceFourthFinal j| <=
        fourthDiscrepancy j)
    (hkineticSecond : IsKineticEulerTrajectory kineticSecond step Qsecond)
    (hkineticFourth : IsKineticEulerTrajectory kineticFourth step Qfourth)
    (hQsecond : forall x y,
      |Qsecond x - Qsecond y| <= Lsecond * |x - y|)
    (hQfourth : forall x y,
      |Qfourth x - Qfourth y| <= Lfourth * |x - y|)
    (K : Nat) :
    |actualSecond K - kineticSecond K| <=
        (|actualSecond 0 - kineticSecond 0| +
          ∑ j ∈ Finset.range K,
            (referenceSecondDefect j +
              (2 + step * Lsecond) * secondDiscrepancy j)) *
          Real.exp (Lsecond * step * (K : Real)) /\
      |actualFourth K - kineticFourth K| <=
        (|actualFourth 0 - kineticFourth 0| +
          ∑ j ∈ Finset.range K,
            (referenceFourthDefect j +
              (2 + step * Lfourth) * fourthDiscrepancy j)) *
          Real.exp (Lfourth * step * (K : Real)) := by
  constructor
  · exact shiftedBlock_commonMomentDiscrepancy_expBound
      actualSecond kineticSecond referenceSecondInitial referenceSecondFinal
      Qsecond step Lsecond referenceSecondDefect secondDiscrepancy
      hstep hLsecond hreferenceSecondDefect hsecondDiscrepancy
      hreferenceSecond hsecondInitial hsecondFinal hkineticSecond hQsecond K
  · exact shiftedBlock_commonMomentDiscrepancy_expBound
      actualFourth kineticFourth referenceFourthInitial referenceFourthFinal
      Qfourth step Lfourth referenceFourthDefect fourthDiscrepancy
      hstep hLfourth hreferenceFourthDefect hfourthDiscrepancy
      hreferenceFourth hfourthInitial hfourthFinal hkineticFourth hQfourth K

end

end ArchonPhysics.PhyslibFPUTShiftedBlockMomentDiscrepancyTelescoping
