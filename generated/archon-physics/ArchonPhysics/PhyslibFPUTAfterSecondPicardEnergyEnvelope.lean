import ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
import ArchonPhysics.ExplicitRandomMassAcousticGap

/-!
# A deterministic energy envelope for the exact post-second-Picard remainder

This file starts from the exact microscopic remainder in
`PhyslibFPUTSecondPicardHistoryBridge`.  The estimates below are direct
finite-sum and triangle-inequality bounds; no RPA, diagram-remainder, kinetic
equation, or independent-frequency hypothesis is used.

The resulting estimate is intentionally coarse.  Its role is also negative:
on the kinetic window `T = L / g^2`, energy coercivity alone does not make the
absolute-value envelope small.
-/

namespace ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope

open UnitAddTorus
open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.ExplicitRandomMassAcousticGap
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- Finite `l1` size of a real modal configuration. -/
def modalAbsSum {N : Nat} [NeZero N]
    (x : WeightedConfiguration N) : Real :=
  ∑ mode, |x mode|

/-- Literal absolute mass of the ordered interaction-tensor row with one
observed leg.  It is finite at every fixed volume. -/
def observedInteractionTensorAbsMass {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N) : Real :=
  ∑ modes : Fin n → Lattice.Site N,
    |interactionTensor m (n + 1) (Fin.cons observed modes)|

theorem modal_coordinate_abs_le_modalAbsSum
    {N : Nat} [NeZero N] (x : WeightedConfiguration N)
    (mode : Lattice.Site N) :
    |x mode| ≤ modalAbsSum x := by
  unfold modalAbsSum
  exact Finset.single_le_sum (fun i _hi ↦ abs_nonneg (x i))
    (Finset.mem_univ mode)

theorem abs_modal_product_le_pow_modalAbsSum
    {N n : Nat} [NeZero N] (x : WeightedConfiguration N)
    (modes : Fin n → Lattice.Site N) :
    |∏ r, x (modes r)| ≤ modalAbsSum x ^ n := by
  rw [Finset.abs_prod]
  calc
    ∏ r, |x (modes r)| ≤ ∏ _r : Fin n, modalAbsSum x := by
      apply Finset.prod_le_prod
      · intro i hi
        exact abs_nonneg (x (modes i))
      · intro i hi
        exact modal_coordinate_abs_le_modalAbsSum x (modes i)
    _ = modalAbsSum x ^ n := by simp

/-- Direct absolute-value bound for an arbitrary ordered tensor contraction. -/
theorem abs_distinguishedTensorContraction_le
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (x : WeightedConfiguration N) :
    |distinguishedTensorContraction m x observed n| ≤
      observedInteractionTensorAbsMass (n := n) m observed *
        modalAbsSum x ^ n := by
  classical
  unfold distinguishedTensorContraction observedInteractionTensorAbsMass
  calc
    |∑ modes : Fin n → Lattice.Site N,
        interactionTensor m (n + 1) (Fin.cons observed modes) *
          ∏ r, x (modes r)| ≤
        ∑ modes : Fin n → Lattice.Site N,
          |interactionTensor m (n + 1) (Fin.cons observed modes) *
            ∏ r, x (modes r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ modes : Fin n → Lattice.Site N,
          |interactionTensor m (n + 1) (Fin.cons observed modes)| *
            modalAbsSum x ^ n := by
      apply Finset.sum_le_sum
      intro modes hmodes
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_modal_product_le_pow_modalAbsSum x modes) (abs_nonneg _)
    _ = (∑ modes : Fin n → Lattice.Site N,
          |interactionTensor m (n + 1) (Fin.cons observed modes)|) *
            modalAbsSum x ^ n := by rw [Finset.sum_mul]

/-- Direct bound for the two ordered placements in the quadratic cross
contraction. -/
theorem abs_quadraticTensorCrossContraction_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (base defect : WeightedConfiguration N) :
    |quadraticTensorCrossContraction m observed base defect| ≤
      2 * observedInteractionTensorAbsMass (n := 2) m observed *
        modalAbsSum base * modalAbsSum defect := by
  classical
  unfold quadraticTensorCrossContraction observedInteractionTensorAbsMass
  calc
    |∑ modes : Fin 2 → Lattice.Site N,
        interactionTensor m 3 (Fin.cons observed modes) *
          (base (modes 0) * defect (modes 1) +
            defect (modes 0) * base (modes 1))| ≤
        ∑ modes : Fin 2 → Lattice.Site N,
          |interactionTensor m 3 (Fin.cons observed modes) *
            (base (modes 0) * defect (modes 1) +
              defect (modes 0) * base (modes 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ modes : Fin 2 → Lattice.Site N,
          |interactionTensor m 3 (Fin.cons observed modes)| *
            (2 * modalAbsSum base * modalAbsSum defect) := by
      apply Finset.sum_le_sum
      intro modes hmodes
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        |base (modes 0) * defect (modes 1) +
            defect (modes 0) * base (modes 1)| ≤
            |base (modes 0) * defect (modes 1)| +
              |defect (modes 0) * base (modes 1)| := abs_add_le _ _
        _ ≤ modalAbsSum base * modalAbsSum defect +
              modalAbsSum defect * modalAbsSum base := by
          rw [abs_mul, abs_mul]
          exact add_le_add
            (mul_le_mul
              (modal_coordinate_abs_le_modalAbsSum base (modes 0))
              (modal_coordinate_abs_le_modalAbsSum defect (modes 1))
              (abs_nonneg _) (by unfold modalAbsSum; positivity))
            (mul_le_mul
              (modal_coordinate_abs_le_modalAbsSum defect (modes 0))
              (modal_coordinate_abs_le_modalAbsSum base (modes 1))
              (abs_nonneg _) (by unfold modalAbsSum; positivity))
        _ = 2 * modalAbsSum base * modalAbsSum defect := by ring
    _ = (∑ modes : Fin 2 → Lattice.Site N,
          |interactionTensor m 3 (Fin.cons observed modes)|) *
            (2 * modalAbsSum base * modalAbsSum defect) := by
      rw [Finset.sum_mul]
    _ = 2 * (∑ modes : Fin 2 → Lattice.Site N,
          |interactionTensor m 3 (Fin.cons observed modes)|) *
            modalAbsSum base * modalAbsSum defect := by
      ring

theorem modalAbsSum_nonneg {N : Nat} [NeZero N]
    (x : WeightedConfiguration N) : 0 ≤ modalAbsSum x := by
  unfold modalAbsSum
  positivity

theorem modalAbsSum_sub_le
    {N : Nat} [NeZero N] (x y : WeightedConfiguration N) :
    modalAbsSum (x - y) ≤ modalAbsSum x + modalAbsSum y := by
  unfold modalAbsSum
  simp only [PiLp.sub_apply]
  calc
    ∑ mode, |x mode - y mode| ≤
        ∑ mode, (|x mode| + |y mode|) := by
      exact Finset.sum_le_sum fun mode _hmode ↦ abs_sub _ _
    _ = (∑ mode, |x mode|) + ∑ mode, |y mode| :=
      Finset.sum_add_distrib

theorem modalAbsSum_smul
    {N : Nat} [NeZero N] (a : Real) (x : WeightedConfiguration N) :
    modalAbsSum (a • x) = |a| * modalAbsSum x := by
  unfold modalAbsSum
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

/-- Free real-mode rotation never enlarges the radius `l1` mass. -/
theorem modalAbsSum_freeWeightedConfiguration_le
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    modalAbsSum (freeWeightedConfiguration radius frequency time phase) ≤
      ∑ mode, |radius mode| := by
  unfold modalAbsSum
  apply Finset.sum_le_sum
  intro mode hmode
  rw [freeWeightedConfiguration_apply]
  unfold freeRealModeCoordinate realPhaseModeCoordinate
  rw [abs_mul]
  calc
    |radius mode| *
        |(unitPhase (physicalFreePhaseEvolution frequency time phase mode)).re| ≤
        |radius mode| * 1 := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        |(unitPhase
            (physicalFreePhaseEvolution frequency time phase mode)).re| ≤
            ‖unitPhase
              (physicalFreePhaseEvolution frequency time phase mode)‖ :=
          Complex.abs_re_le_norm _
        _ = 1 := norm_unitPhase _
    _ = |radius mode| := mul_one _

private theorem abs_le_sq_add_one (x : Real) :
    |x| ≤ x ^ 2 + 1 := by
  rw [← sq_abs]
  nlinarith [sq_nonneg (|x| - (1 / 2 : Real))]

/-- A deliberately coarse finite-dimensional `l2`-to-`l1` estimate which
avoids introducing a square root into later energy envelopes. -/
theorem modalAbsSum_le_card_mul_sqBound_add_one
    {N : Nat} [NeZero N] (x : WeightedConfiguration N) (B : Real)
    (hB : ∑ mode, x mode ^ 2 ≤ B) :
    modalAbsSum x ≤ (N : Real) * (B + 1) := by
  unfold modalAbsSum
  calc
    ∑ mode, |x mode| ≤ ∑ _mode : Lattice.Site N, (B + 1) := by
      apply Finset.sum_le_sum
      intro mode hmode
      calc
        |x mode| ≤ x mode ^ 2 + 1 := abs_le_sq_add_one _
        _ ≤ B + 1 := by
          have hcoord := (Finset.single_le_sum
            (fun i _hi ↦ sq_nonneg (x i)) (Finset.mem_univ mode)).trans hB
          linarith
    _ = (N : Real) * (B + 1) := by
      simp [ZMod.card]
      ring

/-- Parseval plus the square-root mass transform identifies the squared
actual modal position with the physical mass-square sum. -/
theorem sum_sq_modalCoordinates_sqrtMassTransform_eq_massSquareSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : HilbertConfiguration N) :
    ∑ mode, (modalCoordinates m (sqrtMassTransform m q) mode) ^ 2 =
      massSquareSum m (asConfiguration q) := by
  rw [sum_sq_modalCoordinates, EuclideanSpace.real_norm_sq_eq]
  unfold massSquareSum asConfiguration
  apply Finset.sum_congr rfl
  intro i hi
  rw [sqrtMassTransform_apply]
  have hsqrt : Real.sqrt (m.mass i) ^ 2 = m.mass i :=
    Real.sq_sqrt (m.mass_pos i).le
  rw [mul_pow, hsqrt]

/-- Explicit physical-position modal `l1` envelope obtained only from a
mass upper bound, the translation gauge, and a Hamiltonian energy bound. -/
def actualModalEnergyL1Envelope
    (N : Nat) (mUpper kappa beta H : Real) : Real :=
  (N : Real) *
    (4 * mUpper * (N : Real) ^ 3 *
      (H / CoerciveCubicPotential.coercivityConstant kappa beta) + 1)

theorem modalAbsSum_actual_le_energyEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (p q : HilbertConfiguration N)
    (hgauge : ∑ i, m.mass i * asConfiguration q i = 0)
    (henergy : CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration p) (asConfiguration q) ≤ H) :
    modalAbsSum (modalCoordinates m (sqrtMassTransform m q)) ≤
      actualModalEnergyL1Envelope N mUpper kappa beta H := by
  have hc : 0 < CoerciveCubicPotential.coercivityConstant kappa beta :=
    CoerciveCubicPotential.coercivityConstant_pos hbeta
  have hbond : bondSquareSum (asConfiguration q) ≤
      H / CoerciveCubicPotential.coercivityConstant kappa beta := by
    exact (CoerciveLatticeEnergy.sum_sq_forwardDifference_le_energy_div
      m hbeta g (asConfiguration p) (asConfiguration q)).trans
        (div_le_div_of_nonneg_right henergy hc.le)
  have hmass :=
    massSquareSum_le_four_massUpper_mul_cube_bondSquareSum
      m mUpper hmUpper0 hmassUpper (asConfiguration q) hgauge
  have hmassBound : massSquareSum m (asConfiguration q) ≤
      4 * mUpper * (N : Real) ^ 3 *
        (H / CoerciveCubicPotential.coercivityConstant kappa beta) := by
    exact hmass.trans (mul_le_mul_of_nonneg_left hbond (by positivity))
  apply modalAbsSum_le_card_mul_sqBound_add_one
  rw [sum_sq_modalCoordinates_sqrtMassTransform_eq_massSquareSum]
  exact hmassBound

/-! ## Pointwise bounds for the three exact remainder sources -/

def actualHistoryL1 {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q : Time → HilbertConfiguration N) (time : Real) : Real :=
  modalAbsSum (physlibActualModalHistory m q time)

def freeHistoryL1 {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Real :=
  modalAbsSum
    (freeWeightedConfiguration radius (modeFrequency m) time phase)

def firstPicardHistoryL1 {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Real :=
  modalAbsSum
    (physlibQuadraticFirstPicardModalHistory m kappa radius phase time)

def historyDefectL1Envelope {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Real :=
  actualHistoryL1 m q time + freeHistoryL1 m radius phase time

def afterFirstPicardHistoryL1Envelope {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Real :=
  historyDefectL1Envelope m q radius phase time +
    |g| * firstPicardHistoryL1 m kappa radius phase time

theorem modalAbsSum_physlibModalHistoryDefect_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    modalAbsSum (physlibModalHistoryDefect m q radius phase time) ≤
      historyDefectL1Envelope m q radius phase time := by
  unfold physlibModalHistoryDefect historyDefectL1Envelope
    actualHistoryL1 freeHistoryL1
  exact modalAbsSum_sub_le (N := N) _ _

theorem modalAbsSum_physlibModalHistoryAfterFirstPicardRemainder_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    modalAbsSum
        (physlibModalHistoryAfterFirstPicardRemainder
          m kappa g q radius phase time) ≤
      afterFirstPicardHistoryL1Envelope
        m kappa g q radius phase time := by
  unfold physlibModalHistoryAfterFirstPicardRemainder
    afterFirstPicardHistoryL1Envelope firstPicardHistoryL1
  calc
    modalAbsSum
        (physlibModalHistoryDefect m q radius phase time -
          g • physlibQuadraticFirstPicardModalHistory
            m kappa radius phase time) ≤
        modalAbsSum (physlibModalHistoryDefect m q radius phase time) +
          modalAbsSum (g • physlibQuadraticFirstPicardModalHistory
            m kappa radius phase time) := modalAbsSum_sub_le _ _
    _ ≤ historyDefectL1Envelope m q radius phase time +
          |g| * modalAbsSum (physlibQuadraticFirstPicardModalHistory
            m kappa radius phase time) := by
      rw [modalAbsSum_smul]
      exact add_le_add
        (modalAbsSum_physlibModalHistoryDefect_le
          m q radius phase time) le_rfl

/-- Exact norm conversion for a real force in the positive-frequency source
convention. -/
theorem norm_forcedModeSource
    {omega : Real} (_homega : 0 < omega) (force : Real) :
    ‖forcedModeSource omega force‖ =
      |force| / Real.sqrt (2 * omega) := by
  have hsqrt : 0 ≤ Real.sqrt (2 * omega) := Real.sqrt_nonneg _
  simp only [forcedModeSource, norm_div, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, one_mul, abs_of_nonneg hsqrt]

theorem norm_quadraticLinearHistoryRemainderRotatedSource_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (homega : 0 < modeFrequency m observed) :
    ‖physlibQuadraticLinearHistoryRemainderRotatedSource
        m kappa g observed q radius phase time‖ ≤
      (|kappa| * |g| *
        (2 * observedInteractionTensorAbsMass (n := 2) m observed *
          freeHistoryL1 m radius phase time *
          afterFirstPicardHistoryL1Envelope
            m kappa g q radius phase time)) /
        Real.sqrt (2 * modeFrequency m observed) := by
  unfold physlibQuadraticLinearHistoryRemainderRotatedSource
  rw [norm_mul, norm_phaseFactor, one_mul,
    norm_forcedModeSource homega]
  have hcross := abs_quadraticTensorCrossContraction_le
    m observed
      (freeWeightedConfiguration radius (modeFrequency m) time phase)
      (physlibModalHistoryAfterFirstPicardRemainder
        m kappa g q radius phase time)
  have hremainder :=
    modalAbsSum_physlibModalHistoryAfterFirstPicardRemainder_le
      m kappa g q radius phase time
  have hproduct :
      |quadraticTensorCrossContraction m observed
          (freeWeightedConfiguration radius (modeFrequency m) time phase)
          (physlibModalHistoryAfterFirstPicardRemainder
            m kappa g q radius phase time)| ≤
        2 * observedInteractionTensorAbsMass (n := 2) m observed *
          freeHistoryL1 m radius phase time *
          afterFirstPicardHistoryL1Envelope
            m kappa g q radius phase time := by
    have hmass : 0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
      unfold observedInteractionTensorAbsMass
      positivity
    have hfree : 0 ≤ freeHistoryL1 m radius phase time := by
      unfold freeHistoryL1
      exact modalAbsSum_nonneg _
    exact hcross.trans
      (mul_le_mul_of_nonneg_left hremainder
        (mul_nonneg (mul_nonneg (by norm_num) hmass) hfree))
  rw [abs_neg, abs_mul, abs_mul]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_left hproduct (by positivity)

theorem norm_quadraticDefectSquareRotatedSource_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (homega : 0 < modeFrequency m observed) :
    ‖physlibQuadraticDefectSquareRotatedSource
        m kappa g observed q radius phase time‖ ≤
      (|kappa| * |g| *
        (observedInteractionTensorAbsMass (n := 2) m observed *
          historyDefectL1Envelope m q radius phase time ^ 2)) /
        Real.sqrt (2 * modeFrequency m observed) := by
  unfold physlibQuadraticDefectSquareRotatedSource
  rw [norm_mul, norm_phaseFactor, one_mul,
    norm_forcedModeSource homega]
  have hdefect := modalAbsSum_physlibModalHistoryDefect_le
    m q radius phase time
  have hdefect0 :
      0 ≤ modalAbsSum
        (physlibModalHistoryDefect m q radius phase time) :=
    modalAbsSum_nonneg _
  have henvelope0 :
      0 ≤ historyDefectL1Envelope m q radius phase time := by
    unfold historyDefectL1Envelope actualHistoryL1 freeHistoryL1
    exact add_nonneg (modalAbsSum_nonneg _) (modalAbsSum_nonneg _)
  have hsquare :
      modalAbsSum (physlibModalHistoryDefect m q radius phase time) ^ 2 ≤
        historyDefectL1Envelope m q radius phase time ^ 2 := by
    nlinarith
  have hcontraction := abs_distinguishedTensorContraction_le
    m observed (physlibModalHistoryDefect m q radius phase time) (n := 2)
  have hmass :
      0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hproduct :
      |distinguishedTensorContraction m
          (physlibModalHistoryDefect m q radius phase time) observed 2| ≤
        observedInteractionTensorAbsMass (n := 2) m observed *
          historyDefectL1Envelope m q radius phase time ^ 2 :=
    hcontraction.trans (mul_le_mul_of_nonneg_left hsquare hmass)
  rw [abs_neg, abs_mul, abs_mul]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_left hproduct (by positivity)

theorem norm_physlibCubicRotatedSource_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N) (time : Real)
    (homega : 0 < modeFrequency m observed) :
    ‖physlibCubicRotatedSource m beta g observed q time‖ ≤
      (|beta| * g ^ 2 *
        (observedInteractionTensorAbsMass (n := 3) m observed *
          actualHistoryL1 m q time ^ 3)) /
        Real.sqrt (2 * modeFrequency m observed) := by
  unfold physlibCubicRotatedSource physlibModeRotatedSource
    PhyslibHamiltonDuhamel.physlibModeTensorForce tensorNonlinearForce
  rw [norm_mul, norm_phaseFactor, one_mul,
    norm_forcedModeSource homega]
  have hcontraction := abs_distinguishedTensorContraction_le
    m observed (physlibActualModalHistory m q time) (n := 3)
  change
    |-(0 * g * distinguishedTensorContraction m
          (physlibActualModalHistory m q time) observed 2) -
        beta * g ^ 2 * distinguishedTensorContraction m
          (physlibActualModalHistory m q time) observed 3| /
        Real.sqrt (2 * modeFrequency m observed) ≤ _
  simp only [zero_mul, neg_zero, zero_sub, abs_neg, abs_mul]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  simpa [actualHistoryL1, abs_pow] using
    (mul_le_mul_of_nonneg_left hcontraction
      (mul_nonneg (abs_nonneg beta) (sq_nonneg g)))

theorem norm_physlibFreeCubicSecondPicardRotatedSource_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (homega : 0 < modeFrequency m observed) :
    ‖physlibFreeCubicSecondPicardRotatedSource
        m beta observed radius phase time‖ ≤
      (|beta| *
        (observedInteractionTensorAbsMass (n := 3) m observed *
          freeHistoryL1 m radius phase time ^ 3)) /
        Real.sqrt (2 * modeFrequency m observed) := by
  unfold physlibFreeCubicSecondPicardRotatedSource
  rw [norm_mul, norm_phaseFactor, one_mul,
    norm_forcedModeSource homega]
  have hcontraction := abs_distinguishedTensorContraction_le
    m observed
      (freeWeightedConfiguration radius (modeFrequency m) time phase) (n := 3)
  rw [abs_neg, abs_mul]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  simpa [freeHistoryL1] using
    (mul_le_mul_of_nonneg_left hcontraction (abs_nonneg beta))

theorem norm_cubicHistoryRemainderRotatedSource_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (homega : 0 < modeFrequency m observed) :
    ‖physlibCubicHistoryRemainderRotatedSource
        m beta g observed q radius phase time‖ ≤
      (|beta| * g ^ 2 *
        (observedInteractionTensorAbsMass (n := 3) m observed *
          (actualHistoryL1 m q time ^ 3 +
            freeHistoryL1 m radius phase time ^ 3))) /
        Real.sqrt (2 * modeFrequency m observed) := by
  have hactual := norm_physlibCubicRotatedSource_le
    m beta g observed q time homega
  have hfree := norm_physlibFreeCubicSecondPicardRotatedSource_le
    m beta observed radius phase time homega
  unfold physlibCubicHistoryRemainderRotatedSource
  calc
    ‖physlibCubicRotatedSource m beta g observed q time -
        ((g ^ 2 : Real) : Complex) *
          physlibFreeCubicSecondPicardRotatedSource
            m beta observed radius phase time‖ ≤
        ‖physlibCubicRotatedSource m beta g observed q time‖ +
          ‖((g ^ 2 : Real) : Complex) *
            physlibFreeCubicSecondPicardRotatedSource
              m beta observed radius phase time‖ := norm_sub_le _ _
    _ = ‖physlibCubicRotatedSource m beta g observed q time‖ +
          g ^ 2 * ‖physlibFreeCubicSecondPicardRotatedSource
            m beta observed radius phase time‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg g)]
    _ ≤ (|beta| * g ^ 2 *
            (observedInteractionTensorAbsMass (n := 3) m observed *
              actualHistoryL1 m q time ^ 3)) /
            Real.sqrt (2 * modeFrequency m observed) +
          g ^ 2 *
            ((|beta| *
              (observedInteractionTensorAbsMass (n := 3) m observed *
                freeHistoryL1 m radius phase time ^ 3)) /
              Real.sqrt (2 * modeFrequency m observed)) := by
      exact add_le_add hactual
        (mul_le_mul_of_nonneg_left hfree (sq_nonneg g))
    _ = (|beta| * g ^ 2 *
          (observedInteractionTensorAbsMass (n := 3) m observed *
            (actualHistoryL1 m q time ^ 3 +
              freeHistoryL1 m radius phase time ^ 3))) /
          Real.sqrt (2 * modeFrequency m observed) := by ring

/-- Literal pointwise absolute-value envelope for the exact microscopic
source left after extracting the complete second Picard coefficient. -/
def afterSecondPicardSourceEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) : Real :=
  ((|kappa| * |g| *
      (2 * observedInteractionTensorAbsMass (n := 2) m observed *
        freeHistoryL1 m radius phase time *
        afterFirstPicardHistoryL1Envelope
          m kappa g q radius phase time)) +
    (|kappa| * |g| *
      (observedInteractionTensorAbsMass (n := 2) m observed *
        historyDefectL1Envelope m q radius phase time ^ 2)) +
    (|beta| * g ^ 2 *
      (observedInteractionTensorAbsMass (n := 3) m observed *
        (actualHistoryL1 m q time ^ 3 +
          freeHistoryL1 m radius phase time ^ 3)))) /
    Real.sqrt (2 * modeFrequency m observed)

theorem norm_afterSecondPicardRemainderRotatedSource_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (homega : 0 < modeFrequency m observed) :
    ‖physlibFPUTAfterSecondPicardRemainderRotatedSource
        m kappa beta g observed q radius phase time‖ ≤
      afterSecondPicardSourceEnvelope
        m kappa beta g observed q radius phase time := by
  have hlinear := norm_quadraticLinearHistoryRemainderRotatedSource_le
    m kappa g observed q radius phase time homega
  have hsquare := norm_quadraticDefectSquareRotatedSource_le
    m kappa g observed q radius phase time homega
  have hcubic := norm_cubicHistoryRemainderRotatedSource_le
    m beta g observed q radius phase time homega
  unfold physlibFPUTAfterSecondPicardRemainderRotatedSource
    afterSecondPicardSourceEnvelope
  calc
    ‖physlibQuadraticLinearHistoryRemainderRotatedSource
          m kappa g observed q radius phase time +
        physlibQuadraticDefectSquareRotatedSource
          m kappa g observed q radius phase time +
        physlibCubicHistoryRemainderRotatedSource
          m beta g observed q radius phase time‖ ≤
      ‖physlibQuadraticLinearHistoryRemainderRotatedSource
          m kappa g observed q radius phase time‖ +
        ‖physlibQuadraticDefectSquareRotatedSource
          m kappa g observed q radius phase time‖ +
        ‖physlibCubicHistoryRemainderRotatedSource
          m beta g observed q radius phase time‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      calc
        _ ≤
            ((|kappa| * |g| *
              (2 * observedInteractionTensorAbsMass (n := 2) m observed *
                freeHistoryL1 m radius phase time *
                afterFirstPicardHistoryL1Envelope
                  m kappa g q radius phase time)) /
                Real.sqrt (2 * modeFrequency m observed)) +
            ((|kappa| * |g| *
              (observedInteractionTensorAbsMass (n := 2) m observed *
                historyDefectL1Envelope m q radius phase time ^ 2)) /
                Real.sqrt (2 * modeFrequency m observed)) +
            ((|beta| * g ^ 2 *
              (observedInteractionTensorAbsMass (n := 3) m observed *
                (actualHistoryL1 m q time ^ 3 +
                  freeHistoryL1 m radius phase time ^ 3))) /
                Real.sqrt (2 * modeFrequency m observed)) :=
          add_le_add (add_le_add hlinear hsquare) hcubic
        _ = _ := by ring

/-! ## Explicit growth of the reconstructed first Picard history -/

def radiusL1 {N : Nat} [NeZero N]
    (radius : Lattice.Site N → Real) : Real :=
  ∑ mode, |radius mode|

theorem norm_freeQuadraticPicardIntegrand_physlib_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (homega : 0 < modeFrequency m observed) :
    ‖freeQuadraticPicardIntegrand
        (physlibQuadraticCoupling m kappa 1 observed *
          phaseFactor (modeFrequency m observed * time))
        m observed radius (modeFrequency m) time phase‖ ≤
      (|kappa| / Real.sqrt (2 * modeFrequency m observed)) *
        (observedInteractionTensorAbsMass (n := 2) m observed *
          radiusL1 radius ^ 2) := by
  unfold freeQuadraticPicardIntegrand
  rw [norm_mul, norm_mul, norm_phaseFactor, mul_one]
  have hcoupling :
      ‖physlibQuadraticCoupling m kappa 1 observed‖ =
        |kappa| / Real.sqrt (2 * modeFrequency m observed) := by
    unfold physlibQuadraticCoupling
    rw [norm_forcedModeSource homega]
    simp
  rw [hcoupling]
  rw [freeQuadraticTensorSource_eq_complex_tensorContraction,
    Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hcontraction := abs_distinguishedTensorContraction_le
    m observed
      (freeWeightedConfiguration radius (modeFrequency m) time phase) (n := 2)
  have hfree := modalAbsSum_freeWeightedConfiguration_le
    radius (modeFrequency m) time phase
  have hfree0 :
      0 ≤ modalAbsSum
        (freeWeightedConfiguration radius (modeFrequency m) time phase) :=
    modalAbsSum_nonneg _
  have hradius0 : 0 ≤ radiusL1 radius := by
    unfold radiusL1
    positivity
  have hsquare :
      modalAbsSum
          (freeWeightedConfiguration radius (modeFrequency m) time phase) ^ 2 ≤
        radiusL1 radius ^ 2 := by
    unfold radiusL1 at hfree ⊢
    nlinarith
  exact hcontraction.trans
    (mul_le_mul_of_nonneg_left hsquare (by
      unfold observedInteractionTensorAbsMass
      positivity))

theorem norm_physlibQuadraticFirstPicardCoefficient_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    ‖physlibQuadraticFirstPicardCoefficient
        m kappa radius phase time observed‖ ≤
      ((|kappa| / Real.sqrt (2 * modeFrequency m observed)) *
        (observedInteractionTensorAbsMass (n := 2) m observed *
          radiusL1 radius ^ 2)) * |time| := by
  unfold physlibQuadraticFirstPicardCoefficient
    freeQuadraticInteractionPictureCorrection
  calc
    ‖∫ s in (0 : Real)..time,
        freeQuadraticPicardIntegrand
          (physlibQuadraticCoupling m kappa 1 observed *
            phaseFactor (modeFrequency m observed * s))
          m observed radius (modeFrequency m) s phase‖ ≤
      ((|kappa| / Real.sqrt (2 * modeFrequency m observed)) *
        (observedInteractionTensorAbsMass (n := 2) m observed *
          radiusL1 radius ^ 2)) * |time - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      exact norm_freeQuadraticPicardIntegrand_physlib_le
        m kappa observed radius phase s homega
    _ = _ := by rw [sub_zero]

def firstPicardModalL1Rate {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) : Real :=
  ∑ observed : Lattice.Site N,
    if 0 < modeFrequency m observed then
      |kappa| * observedInteractionTensorAbsMass (n := 2) m observed *
        radiusL1 radius ^ 2 / modeFrequency m observed
    else 0

theorem abs_physlibQuadraticFirstPicardModalHistory_apply_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N)
    (homega : 0 < modeFrequency m observed) :
    |physlibQuadraticFirstPicardModalHistory
        m kappa radius phase time observed| ≤
      (|kappa| * observedInteractionTensorAbsMass (n := 2) m observed *
        radiusL1 radius ^ 2 / modeFrequency m observed) * |time| := by
  rw [physlibQuadraticFirstPicardModalHistory_apply]
  unfold interactionPictureCorrectionCoordinate
  have hcoefficient := norm_physlibQuadraticFirstPicardCoefficient_le
    m kappa radius phase time observed homega
  have hsqrt : 0 < Real.sqrt (2 * modeFrequency m observed) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) homega)
  have hre :
      |(phaseRenormalize (-(modeFrequency m observed * time))
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed)).re| ≤
        ‖physlibQuadraticFirstPicardCoefficient
          m kappa radius phase time observed‖ := by
    calc
      |(phaseRenormalize (-(modeFrequency m observed * time))
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase time observed)).re| ≤
          ‖phaseRenormalize (-(modeFrequency m observed * time))
            (physlibQuadraticFirstPicardCoefficient
              m kappa radius phase time observed)‖ := Complex.abs_re_le_norm _
      _ = ‖physlibQuadraticFirstPicardCoefficient
              m kappa radius phase time observed‖ := by
        unfold phaseRenormalize
        rw [norm_mul, norm_phaseFactor, one_mul]
  rw [abs_div, abs_mul, abs_of_pos homega, abs_of_nonneg hsqrt.le]
  calc
    Real.sqrt (2 * modeFrequency m observed) *
          |(phaseRenormalize (-(modeFrequency m observed * time))
            (physlibQuadraticFirstPicardCoefficient
              m kappa radius phase time observed)).re| /
        modeFrequency m observed ≤
      Real.sqrt (2 * modeFrequency m observed) *
          (((|kappa| / Real.sqrt (2 * modeFrequency m observed)) *
            (observedInteractionTensorAbsMass (n := 2) m observed *
              radiusL1 radius ^ 2)) * |time|) /
        modeFrequency m observed := by
      apply div_le_div_of_nonneg_right _ homega.le
      exact mul_le_mul_of_nonneg_left (hre.trans hcoefficient) hsqrt.le
    _ = (|kappa| *
          observedInteractionTensorAbsMass (n := 2) m observed *
          radiusL1 radius ^ 2 / modeFrequency m observed) * |time| := by
      field_simp [ne_of_gt homega, ne_of_gt hsqrt]

theorem firstPicardHistoryL1_le_rate_mul_abs_time
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    firstPicardHistoryL1 m kappa radius phase time ≤
      firstPicardModalL1Rate m kappa radius * |time| := by
  unfold firstPicardHistoryL1 modalAbsSum firstPicardModalL1Rate
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro observed hobserved
  by_cases homega : 0 < modeFrequency m observed
  · rw [if_pos homega]
    exact abs_physlibQuadraticFirstPicardModalHistory_apply_le
      m kappa radius phase time observed homega
  · have hzero : modeFrequency m observed = 0 :=
      le_antisymm (le_of_not_gt homega) (modeFrequency_nonneg m observed)
    rw [if_neg homega, zero_mul,
      physlibQuadraticFirstPicardModalHistory_eq_zero_of_modeFrequency_eq_zero
        m kappa radius phase time observed hzero, abs_zero]

theorem firstPicardModalL1Rate_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) :
    0 ≤ firstPicardModalL1Rate m kappa radius := by
  unfold firstPicardModalL1Rate
  apply Finset.sum_nonneg
  intro observed hobserved
  split_ifs with homega
  · have hmass :
        0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
      unfold observedInteractionTensorAbsMass
      positivity
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg kappa) hmass)
        (sq_nonneg (radiusL1 radius))) homega.le
  · exact le_rfl

theorem actualHistoryL1_le_energyEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (p q : Time → HilbertConfiguration N) (time : Real)
    (hgauge : ∑ i, m.mass i *
        asConfiguration ((realReparametrize q) time) i = 0)
    (henergy : CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) time))
        (asConfiguration ((realReparametrize q) time)) ≤ H) :
    actualHistoryL1 m q time ≤
      actualModalEnergyL1Envelope N mUpper kappa beta H := by
  change modalAbsSum
      (modalCoordinates m
        (sqrtMassTransform m ((realReparametrize q) time))) ≤ _
  exact modalAbsSum_actual_le_energyEnvelope
    m hmUpper0 hmassUpper hbeta
      ((realReparametrize p) time) ((realReparametrize q) time)
      hgauge henergy

/-- Uniform-in-time version of the direct absolute-value source envelope.
The only dynamical input is an actual modal `l1` bound; below it is
instantiated from the Hamiltonian energy and translation gauge. -/
def afterSecondPicardWindowEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (actualBound : Real) (radius : Lattice.Site N → Real)
    (T : Real) : Real :=
  ((|kappa| * |g| *
      (2 * observedInteractionTensorAbsMass (n := 2) m observed *
        radiusL1 radius *
        (actualBound + radiusL1 radius +
          |g| * (firstPicardModalL1Rate m kappa radius * T)))) +
    (|kappa| * |g| *
      (observedInteractionTensorAbsMass (n := 2) m observed *
        (actualBound + radiusL1 radius) ^ 2)) +
    (|beta| * g ^ 2 *
      (observedInteractionTensorAbsMass (n := 3) m observed *
        (actualBound ^ 3 + radiusL1 radius ^ 3)))) /
    Real.sqrt (2 * modeFrequency m observed)

theorem norm_afterSecondPicardRemainderRotatedSource_le_windowEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    {actualBound T time : Real}
    (homega : 0 < modeFrequency m observed)
    (hactual0 : 0 ≤ actualBound) (hT : 0 ≤ T)
    (htime : |time| ≤ T)
    (hactual : actualHistoryL1 m q time ≤ actualBound) :
    ‖physlibFPUTAfterSecondPicardRemainderRotatedSource
        m kappa beta g observed q radius phase time‖ ≤
      afterSecondPicardWindowEnvelope
        m kappa beta g observed actualBound radius T := by
  have hsource := norm_afterSecondPicardRemainderRotatedSource_le
    m kappa beta g observed q radius phase time homega
  have hfree := modalAbsSum_freeWeightedConfiguration_le
    radius (modeFrequency m) time phase
  have hfirst := firstPicardHistoryL1_le_rate_mul_abs_time
    m kappa radius phase time
  have hrate0 := firstPicardModalL1Rate_nonneg m kappa radius
  have hradius0 : 0 ≤ radiusL1 radius := by
    unfold radiusL1
    positivity
  have hfree0 : 0 ≤ freeHistoryL1 m radius phase time := by
    unfold freeHistoryL1
    exact modalAbsSum_nonneg _
  have hactualCurrent0 : 0 ≤ actualHistoryL1 m q time := by
    unfold actualHistoryL1
    exact modalAbsSum_nonneg _
  have hfirst0 : 0 ≤ firstPicardHistoryL1 m kappa radius phase time := by
    unfold firstPicardHistoryL1
    exact modalAbsSum_nonneg _
  have hfreeBound : freeHistoryL1 m radius phase time ≤ radiusL1 radius := by
    simpa [freeHistoryL1, radiusL1] using hfree
  have hfirstBound : firstPicardHistoryL1 m kappa radius phase time ≤
      firstPicardModalL1Rate m kappa radius * T := by
    exact hfirst.trans
      (mul_le_mul_of_nonneg_left htime hrate0)
  have hdefect : historyDefectL1Envelope m q radius phase time ≤
      actualBound + radiusL1 radius := by
    unfold historyDefectL1Envelope
    exact add_le_add hactual hfreeBound
  have hdefect0 :
      0 ≤ historyDefectL1Envelope m q radius phase time := by
    unfold historyDefectL1Envelope
    exact add_nonneg hactualCurrent0 hfree0
  have hdefectBound0 : 0 ≤ actualBound + radiusL1 radius :=
    add_nonneg hactual0 hradius0
  have hafter :
      afterFirstPicardHistoryL1Envelope
          m kappa g q radius phase time ≤
        actualBound + radiusL1 radius +
          |g| * (firstPicardModalL1Rate m kappa radius * T) := by
    unfold afterFirstPicardHistoryL1Envelope
    exact add_le_add hdefect
      (mul_le_mul_of_nonneg_left hfirstBound (abs_nonneg g))
  have hafter0 :
      0 ≤ afterFirstPicardHistoryL1Envelope
        m kappa g q radius phase time := by
    unfold afterFirstPicardHistoryL1Envelope
    exact add_nonneg hdefect0 (mul_nonneg (abs_nonneg g) hfirst0)
  have hafterBound0 :
      0 ≤ actualBound + radiusL1 radius +
        |g| * (firstPicardModalL1Rate m kappa radius * T) := by
    positivity
  have hM2 :
      0 ≤ observedInteractionTensorAbsMass (n := 2) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hM3 :
      0 ≤ observedInteractionTensorAbsMass (n := 3) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hlinearInner :
      2 * observedInteractionTensorAbsMass (n := 2) m observed *
          freeHistoryL1 m radius phase time *
          afterFirstPicardHistoryL1Envelope
            m kappa g q radius phase time ≤
        2 * observedInteractionTensorAbsMass (n := 2) m observed *
          radiusL1 radius *
          (actualBound + radiusL1 radius +
            |g| * (firstPicardModalL1Rate m kappa radius * T)) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hfreeBound
        (mul_nonneg (by norm_num) hM2)
    · exact hafter
    · exact hafter0
    · exact mul_nonneg (mul_nonneg (by norm_num) hM2) hradius0
  have hsquare :
      historyDefectL1Envelope m q radius phase time ^ 2 ≤
        (actualBound + radiusL1 radius) ^ 2 :=
    pow_le_pow_left₀ hdefect0 hdefect 2
  have hcubicPowers :
      actualHistoryL1 m q time ^ 3 +
          freeHistoryL1 m radius phase time ^ 3 ≤
        actualBound ^ 3 + radiusL1 radius ^ 3 := by
    exact add_le_add
      (pow_le_pow_left₀ hactualCurrent0 hactual 3)
      (pow_le_pow_left₀ hfree0 hfreeBound 3)
  unfold afterSecondPicardSourceEnvelope at hsource
  unfold afterSecondPicardWindowEnvelope
  refine hsource.trans ?_
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_left hlinearInner (by positivity))
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsquare hM2) (by positivity)))
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hcubicPowers hM3) (by positivity))

/-- Pointwise Hamiltonian-energy specialization of the window envelope. -/
theorem norm_afterSecondPicardRemainderRotatedSource_le_energyWindow
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T time : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T) (htime : |time| ≤ T)
    (hgauge : ∑ i, m.mass i *
        asConfiguration ((realReparametrize q) time) i = 0)
    (henergy : CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) time))
        (asConfiguration ((realReparametrize q) time)) ≤ H) :
    ‖physlibFPUTAfterSecondPicardRemainderRotatedSource
        m kappa beta g observed q radius phase time‖ ≤
      afterSecondPicardWindowEnvelope m kappa beta g observed
        (actualModalEnergyL1Envelope N mUpper kappa beta H) radius T := by
  have hH : 0 ≤ H :=
    (CoerciveLatticeEnergy.hamiltonian_nonneg m hbeta g
      (asConfiguration ((realReparametrize p) time))
      (asConfiguration ((realReparametrize q) time))).trans henergy
  have hc : 0 < CoerciveCubicPotential.coercivityConstant kappa beta :=
    CoerciveCubicPotential.coercivityConstant_pos hbeta
  have hN : 0 ≤ (N : Real) := by positivity
  have hactualBound0 :
      0 ≤ actualModalEnergyL1Envelope N mUpper kappa beta H := by
    unfold actualModalEnergyL1Envelope
    exact mul_nonneg hN (add_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hmUpper0) (by positivity))
        (div_nonneg hH hc.le)) (by norm_num))
  apply norm_afterSecondPicardRemainderRotatedSource_le_windowEnvelope
    m kappa beta g observed q radius phase homega hactualBound0 hT htime
  exact actualHistoryL1_le_energyEnvelope
    m hmUpper0 hmassUpper hbeta p q time hgauge henergy

/-- The time-integrated exact post-second-Picard coefficient is bounded
directly from the microscopic Hamiltonian energy shell.  No remainder
certificate is an input. -/
theorem norm_afterSecondPicardRemainderCoefficient_le_energyWindow
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ time ∈ Icc 0 T, ∑ i, m.mass i *
        asConfiguration ((realReparametrize q) time) i = 0)
    (henergy : ∀ time ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) time))
        (asConfiguration ((realReparametrize q) time)) ≤ H) :
    ‖physlibFPUTAfterSecondPicardRemainderCoefficient
        m kappa beta g observed q radius phase T‖ ≤
      afterSecondPicardWindowEnvelope m kappa beta g observed
        (actualModalEnergyL1Envelope N mUpper kappa beta H) radius T * T := by
  unfold physlibFPUTAfterSecondPicardRemainderCoefficient
  calc
    ‖∫ time in (0 : Real)..T,
        physlibFPUTAfterSecondPicardRemainderRotatedSource
          m kappa beta g observed q radius phase time‖ ≤
      afterSecondPicardWindowEnvelope m kappa beta g observed
          (actualModalEnergyL1Envelope N mUpper kappa beta H) radius T *
        |T - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro time htime
      have htimeIcc : time ∈ Icc 0 T := by
        simpa only [uIcc_of_le hT] using Set.uIoc_subset_uIcc htime
      apply norm_afterSecondPicardRemainderRotatedSource_le_energyWindow
        m hmUpper0 hmassUpper hbeta observed p q radius phase homega hT
      · exact (abs_le.2 ⟨by linarith [htimeIcc.1], htimeIcc.2⟩)
      · exact hgauge time htimeIcc
      · exact henergy time htimeIcc
    _ = _ := by rw [sub_zero, abs_of_nonneg hT]

/-- Nearest unconditional microscopic-to-second-Picard error theorem.  For a
genuine differentiable Physlib Hamiltonian solution, the norm of the exact
interaction-picture error is bounded by the energy-window envelope above. -/
theorem norm_interactionPicture_physlibMode_sub_twoStep_le_energyWindow
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ time ∈ Icc 0 T, ∑ i, m.mass i *
        asConfiguration ((realReparametrize q) time) i = 0)
    (henergy : ∀ time ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) time))
        (asConfiguration ((realReparametrize q) time)) ≤ H) :
    ‖phaseRenormalize (modeFrequency m observed * T)
          (physlibModeAmplitude m observed p q T) -
        twoStepPerturbedAmplitude g
          (physlibModeAmplitude m observed p q 0)
          (physlibQuadraticFirstPicardCoefficient
            m kappa radius phase T observed)
          (physlibFPUTSecondPicardCoefficient
            m kappa beta observed radius phase T)‖ ≤
      afterSecondPicardWindowEnvelope m kappa beta g observed
        (actualModalEnergyL1Envelope N mUpper kappa beta H) radius T * T := by
  have hexact := interactionPicture_physlibMode_eq_twoStep_add_remainder
    m kappa beta g observed p q hp hq hHamilton homega radius phase T
  have hbound := norm_afterSecondPicardRemainderCoefficient_le_energyWindow
    m hmUpper0 hmassUpper hbeta observed p q radius phase homega hT
      hgauge henergy
  rw [hexact]
  simpa only [add_sub_cancel_left] using hbound

/-! ## What the absolute-value estimate does on kinetic time -/

def energyOnlyLinearIntegratedScale
    (kappa g M2 radiusBound actualBound T : Real) : Real :=
  |kappa| * |g| * (2 * M2 * radiusBound *
    (actualBound + radiusBound)) * T

def firstPicardTriangleIntegratedScale
    (kappa g M2 radiusBound firstPicardRate T : Real) : Real :=
  |kappa| * |g| *
    (2 * M2 * radiusBound * (|g| * (firstPicardRate * T))) * T

/-- The energy-only part of the linear-history triangle estimate is exactly
`O(g⁻¹)` on `T = L/g²`. -/
theorem energyOnlyLinearIntegratedScale_kineticTime
    {kappa g M2 radiusBound actualBound L : Real} (hg : 0 < g) :
    energyOnlyLinearIntegratedScale kappa g M2 radiusBound actualBound
        (L / g ^ 2) =
      2 * |kappa| * M2 * radiusBound * (actualBound + radiusBound) * L / g := by
  unfold energyOnlyLinearIntegratedScale
  rw [abs_of_pos hg]
  field_simp [ne_of_gt hg]

/-- The additional triangle term caused by subtracting the explicitly
growing first Picard history is exactly `O(g⁻²)` on kinetic time. -/
theorem firstPicardTriangleIntegratedScale_kineticTime
    {kappa g M2 radiusBound firstPicardRate L : Real} (hg : 0 < g) :
    firstPicardTriangleIntegratedScale kappa g M2 radiusBound
        firstPicardRate (L / g ^ 2) =
      2 * |kappa| * M2 * radiusBound * firstPicardRate * L ^ 2 / g ^ 2 := by
  unfold firstPicardTriangleIntegratedScale
  rw [abs_of_pos hg]
  field_simp [ne_of_gt hg]

end

end ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
