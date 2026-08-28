import ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow

/-!
# Lipschitz control of the actual-minus-free cubic FPUT history

The previous sharpened post-second-Picard bound still estimated the cubic
history difference by the sum of two cubic sizes.  That triangle estimate
does not vanish when the actual history equals the free history.

This companion module uses the three-factor telescoping identity.  The
resulting cubic source bound is proportional to the real modal-history
defect and therefore gains one further factor of the microscopic coupling
on a fixed short time block.
-/

namespace ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder

open MeasureTheory
open UnitAddTorus
open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTFirstDuhamelEnergyWindow
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSharpRemainderEnergyWindow
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.RandomPhaseMoments
open ArchonPhysics.ReducedModeTransform
open scoped Interval ComplexConjugate

noncomputable section

/-! ## Exact cubic telescoping and its finite-volume Lipschitz bound -/

/-- The ordered three-leg tensor contraction obtained by telescoping from
`free` to `actual`, one input leg at a time. -/
def cubicTensorTelescopingContraction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (actual free : WeightedConfiguration N) : Real :=
  ∑ modes : Fin 3 → Lattice.Site N,
    interactionTensor m 4 (Fin.cons observed modes) *
      ((actual (modes 0) - free (modes 0)) *
          actual (modes 1) * actual (modes 2) +
        free (modes 0) * (actual (modes 1) - free (modes 1)) *
          actual (modes 2) +
        free (modes 0) * free (modes 1) *
          (actual (modes 2) - free (modes 2)))

/-- Exact three-factor telescoping identity for the distinguished cubic
interaction tensor row. -/
theorem distinguishedTensorContraction_three_sub_eq_telescoping
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (actual free : WeightedConfiguration N) :
    distinguishedTensorContraction m actual observed 3 -
        distinguishedTensorContraction m free observed 3 =
      cubicTensorTelescopingContraction m observed actual free := by
  classical
  unfold distinguishedTensorContraction cubicTensorTelescopingContraction
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro modes hmodes
  simp only [Fin.prod_univ_three]
  ring

/-- Cubic tensor contractions are locally Lipschitz in modal `l1`.  The
constant is the literal finite-volume interaction-tensor mass, and the
right side vanishes with `modalAbsSum (actual - free)`. -/
theorem abs_cubicTensorTelescopingContraction_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (actual free : WeightedConfiguration N) :
    |cubicTensorTelescopingContraction m observed actual free| ≤
      observedInteractionTensorAbsMass (n := 3) m observed *
        modalAbsSum (actual - free) *
          (modalAbsSum actual ^ 2 +
            modalAbsSum actual * modalAbsSum free +
            modalAbsSum free ^ 2) := by
  classical
  have hactual0 : 0 ≤ modalAbsSum actual := modalAbsSum_nonneg _
  have hfree0 : 0 ≤ modalAbsSum free := modalAbsSum_nonneg _
  have hdefect0 : 0 ≤ modalAbsSum (actual - free) := modalAbsSum_nonneg _
  unfold cubicTensorTelescopingContraction observedInteractionTensorAbsMass
  calc
    |∑ modes : Fin 3 → Lattice.Site N,
        interactionTensor m 4 (Fin.cons observed modes) *
          ((actual (modes 0) - free (modes 0)) *
              actual (modes 1) * actual (modes 2) +
            free (modes 0) * (actual (modes 1) - free (modes 1)) *
              actual (modes 2) +
            free (modes 0) * free (modes 1) *
              (actual (modes 2) - free (modes 2)))| ≤
      ∑ modes : Fin 3 → Lattice.Site N,
        |interactionTensor m 4 (Fin.cons observed modes) *
          ((actual (modes 0) - free (modes 0)) *
              actual (modes 1) * actual (modes 2) +
            free (modes 0) * (actual (modes 1) - free (modes 1)) *
              actual (modes 2) +
            free (modes 0) * free (modes 1) *
              (actual (modes 2) - free (modes 2)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ modes : Fin 3 → Lattice.Site N,
        |interactionTensor m 4 (Fin.cons observed modes)| *
          (modalAbsSum (actual - free) *
            (modalAbsSum actual ^ 2 +
              modalAbsSum actual * modalAbsSum free +
              modalAbsSum free ^ 2)) := by
      apply Finset.sum_le_sum
      intro modes hmodes
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        |(actual (modes 0) - free (modes 0)) *
              actual (modes 1) * actual (modes 2) +
            free (modes 0) * (actual (modes 1) - free (modes 1)) *
              actual (modes 2) +
            free (modes 0) * free (modes 1) *
              (actual (modes 2) - free (modes 2))| ≤
          |(actual (modes 0) - free (modes 0)) *
              actual (modes 1) * actual (modes 2)| +
            |free (modes 0) * (actual (modes 1) - free (modes 1)) *
              actual (modes 2)| +
            |free (modes 0) * free (modes 1) *
              (actual (modes 2) - free (modes 2))| := by
            exact (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ modalAbsSum (actual - free) *
              modalAbsSum actual * modalAbsSum actual +
            modalAbsSum free * modalAbsSum (actual - free) *
              modalAbsSum actual +
            modalAbsSum free * modalAbsSum free *
              modalAbsSum (actual - free) := by
          simp only [abs_mul]
          apply add_le_add
          · apply add_le_add
            · exact mul_le_mul
                (mul_le_mul
                  (modal_coordinate_abs_le_modalAbsSum
                    (actual - free) (modes 0))
                  (modal_coordinate_abs_le_modalAbsSum actual (modes 1))
                  (abs_nonneg _) hdefect0)
                (modal_coordinate_abs_le_modalAbsSum actual (modes 2))
                (abs_nonneg _) (mul_nonneg hdefect0 hactual0)
            · exact mul_le_mul
                (mul_le_mul
                  (modal_coordinate_abs_le_modalAbsSum free (modes 0))
                  (modal_coordinate_abs_le_modalAbsSum
                    (actual - free) (modes 1))
                  (abs_nonneg _) hfree0)
                (modal_coordinate_abs_le_modalAbsSum actual (modes 2))
                (abs_nonneg _) (mul_nonneg hfree0 hdefect0)
          · exact mul_le_mul
              (mul_le_mul
                (modal_coordinate_abs_le_modalAbsSum free (modes 0))
                (modal_coordinate_abs_le_modalAbsSum free (modes 1))
                (abs_nonneg _) hfree0)
              (modal_coordinate_abs_le_modalAbsSum
                (actual - free) (modes 2))
              (abs_nonneg _) (mul_nonneg hfree0 hfree0)
        _ = modalAbsSum (actual - free) *
            (modalAbsSum actual ^ 2 +
              modalAbsSum actual * modalAbsSum free +
              modalAbsSum free ^ 2) := by ring
    _ = (∑ modes : Fin 3 → Lattice.Site N,
          |interactionTensor m 4 (Fin.cons observed modes)|) *
        (modalAbsSum (actual - free) *
          (modalAbsSum actual ^ 2 +
            modalAbsSum actual * modalAbsSum free +
            modalAbsSum free ^ 2)) := by
      rw [Finset.sum_mul]
    _ = (∑ modes : Fin 3 → Lattice.Site N,
          |interactionTensor m 4 (Fin.cons observed modes)|) *
        modalAbsSum (actual - free) *
          (modalAbsSum actual ^ 2 +
            modalAbsSum actual * modalAbsSum free +
            modalAbsSum free ^ 2) := by ring

/-- Direct Lipschitz estimate for the difference of cubic tensor
contractions. -/
theorem abs_distinguishedTensorContraction_three_sub_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (actual free : WeightedConfiguration N) :
    |distinguishedTensorContraction m actual observed 3 -
        distinguishedTensorContraction m free observed 3| ≤
      observedInteractionTensorAbsMass (n := 3) m observed *
        modalAbsSum (actual - free) *
          (modalAbsSum actual ^ 2 +
            modalAbsSum actual * modalAbsSum free +
            modalAbsSum free ^ 2) := by
  rw [distinguishedTensorContraction_three_sub_eq_telescoping]
  exact abs_cubicTensorTelescopingContraction_le m observed actual free

/-! ## The actual-minus-free cubic source -/

/-- The cubic post-second-Picard source is exactly the forced-mode image of
the difference of the actual and free cubic tensor contractions. -/
theorem physlibCubicHistoryRemainderRotatedSource_eq_tensorDifference
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibCubicHistoryRemainderRotatedSource
        m beta g observed q radius phase time =
      phaseFactor (modeFrequency m observed * time) *
        forcedModeSource (modeFrequency m observed)
          (-(beta * g ^ 2 *
            (distinguishedTensorContraction m
                (physlibActualModalHistory m q time) observed 3 -
              distinguishedTensorContraction m
                (freeWeightedConfiguration
                  radius (modeFrequency m) time phase) observed 3))) := by
  unfold physlibCubicHistoryRemainderRotatedSource
    physlibCubicRotatedSource physlibModeRotatedSource
    physlibModeTensorForce tensorNonlinearForce
    physlibFreeCubicSecondPicardRotatedSource
    physlibActualModalHistory forcedModeSource
  push_cast
  ring

/-- Pointwise cubic source Lipschitz bound with supplied modal `l1` bounds.
The crucial factor `defectBound` replaces the old sum of two cubic sizes. -/
theorem norm_cubicHistoryRemainder_le_lipschitz_l1_bounds
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (homega : 0 < modeFrequency m observed)
    {actualBound freeBound defectBound : Real}
    (hactual : actualHistoryL1 m q time ≤ actualBound)
    (hfree : freeHistoryL1 m radius phase time ≤ freeBound)
    (hdefect : modalAbsSum
      (physlibModalHistoryDefect m q radius phase time) ≤ defectBound) :
    ‖physlibCubicHistoryRemainderRotatedSource
        m beta g observed q radius phase time‖ ≤
      (|beta| * g ^ 2 *
        (observedInteractionTensorAbsMass (n := 3) m observed *
          (defectBound *
            (actualBound ^ 2 + actualBound * freeBound + freeBound ^ 2)))) /
        Real.sqrt (2 * modeFrequency m observed) := by
  let actual := physlibActualModalHistory m q time
  let free := freeWeightedConfiguration
    radius (modeFrequency m) time phase
  have hactual0 : 0 ≤ modalAbsSum actual := modalAbsSum_nonneg _
  have hfree0 : 0 ≤ modalAbsSum free := modalAbsSum_nonneg _
  have hdefect0 : 0 ≤ modalAbsSum (actual - free) := modalAbsSum_nonneg _
  have hactualBound0 : 0 ≤ actualBound := hactual0.trans hactual
  have hfreeBound0 : 0 ≤ freeBound := hfree0.trans hfree
  have hdefect' : modalAbsSum (actual - free) ≤ defectBound := by
    simpa only [actual, free, physlibModalHistoryDefect] using hdefect
  have hpoly :
      modalAbsSum actual ^ 2 +
          modalAbsSum actual * modalAbsSum free + modalAbsSum free ^ 2 ≤
        actualBound ^ 2 + actualBound * freeBound + freeBound ^ 2 := by
    exact add_le_add
      (add_le_add
        (pow_le_pow_left₀ hactual0 hactual 2)
        (mul_le_mul hactual hfree hfree0 hactualBound0))
      (pow_le_pow_left₀ hfree0 hfree 2)
  have hpoly0 : 0 ≤
      modalAbsSum actual ^ 2 +
        modalAbsSum actual * modalAbsSum free + modalAbsSum free ^ 2 := by
    positivity
  have hdefectBound0 : 0 ≤ defectBound := hdefect0.trans hdefect'
  have hproduct :
      modalAbsSum (actual - free) *
          (modalAbsSum actual ^ 2 +
            modalAbsSum actual * modalAbsSum free + modalAbsSum free ^ 2) ≤
        defectBound *
          (actualBound ^ 2 + actualBound * freeBound + freeBound ^ 2) := by
    exact mul_le_mul hdefect' hpoly hpoly0 hdefectBound0
  have hM3 :
      0 ≤ observedInteractionTensorAbsMass (n := 3) m observed := by
    unfold observedInteractionTensorAbsMass
    positivity
  have hcontraction :=
    abs_distinguishedTensorContraction_three_sub_le
      m observed actual free
  have hcontractionBound :
      |distinguishedTensorContraction m actual observed 3 -
          distinguishedTensorContraction m free observed 3| ≤
        observedInteractionTensorAbsMass (n := 3) m observed *
          (defectBound *
            (actualBound ^ 2 + actualBound * freeBound + freeBound ^ 2)) :=
    hcontraction.trans (by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hproduct hM3))
  rw [physlibCubicHistoryRemainderRotatedSource_eq_tensorDifference]
  rw [norm_mul, norm_phaseFactor, one_mul,
    norm_forcedModeSource homega, abs_neg, abs_mul, abs_mul, abs_pow,
    sq_abs]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcontractionBound (by positivity))
    (Real.sqrt_nonneg _)

/-! ## Improved post-second-Picard source and coefficient envelopes -/

/-- Sharpened post-second-Picard source envelope with the cubic history
difference controlled by its Lipschitz defect. -/
def cubicLipschitzAfterSecondPicardSourceWindowEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (freeBound actualBound defectRate afterFirstRate T : Real) : Real :=
  ((|kappa| * |g| *
      (2 * observedInteractionTensorAbsMass (n := 2) m observed *
        freeBound * (afterFirstRate * T))) +
    (|kappa| * |g| *
      (observedInteractionTensorAbsMass (n := 2) m observed *
        (defectRate * T) ^ 2)) +
    (|beta| * g ^ 2 *
      (observedInteractionTensorAbsMass (n := 3) m observed *
        ((defectRate * T) *
          (actualBound ^ 2 + actualBound * freeBound + freeBound ^ 2))))) /
    Real.sqrt (2 * modeFrequency m observed)

/-- Pointwise energy-window specialization of the cubic-Lipschitz
post-second-Picard source. -/
theorem norm_afterSecondPicardRemainderRotatedSource_le_cubicLipschitzWindow
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T time : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (hinitial : ∀ mode,
      physlibModeAmplitude m mode p q 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T) (htime : time ∈ Icc 0 T)
    (hgauge : ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize q) s) i = 0)
    (henergy : ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) s))
        (asConfiguration ((realReparametrize q) s)) ≤ H)
    (hzeroHistory : ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect m q radius phase s mode = 0) :
    ‖physlibFPUTAfterSecondPicardRemainderRotatedSource
        m kappa beta g observed q radius phase time‖ ≤
      cubicLipschitzAfterSecondPicardSourceWindowEnvelope
        m kappa beta g observed (radiusL1 radius)
          (actualModalEnergyL1Envelope N mUpper kappa beta H)
          (sharpHistoryDefectL1Rate m kappa beta g
            (actualModalEnergyL1Envelope N mUpper kappa beta H))
          (sharpAfterFirstPicardHistoryL1Rate
            m kappa beta g (radiusL1 radius)
              (actualModalEnergyL1Envelope N mUpper kappa beta H)
              (sharpHistoryDefectL1Rate m kappa beta g
                (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) T := by
  let actualBound := actualModalEnergyL1Envelope N mUpper kappa beta H
  let defectRate := sharpHistoryDefectL1Rate m kappa beta g actualBound
  let afterFirstRate := sharpAfterFirstPicardHistoryL1Rate
    m kappa beta g (radiusL1 radius) actualBound defectRate T
  have henergy0 := henergy 0 ⟨le_rfl, hT⟩
  have hH : 0 ≤ H :=
    (CoerciveLatticeEnergy.hamiltonian_nonneg m hbeta g
      (asConfiguration ((realReparametrize p) 0))
      (asConfiguration ((realReparametrize q) 0))).trans henergy0
  have hactualBound0 : 0 ≤ actualBound := by
    dsimp only [actualBound]
    unfold actualModalEnergyL1Envelope
    exact mul_nonneg (by positivity) (add_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hmUpper0) (by positivity))
        (div_nonneg hH
          (CoerciveCubicPotential.coercivityConstant_pos hbeta).le))
      (by norm_num))
  have hdefectRate0 : 0 ≤ defectRate :=
    sharpHistoryDefectL1Rate_nonneg
      m kappa beta g actualBound hactualBound0
  have hradius0 : 0 ≤ radiusL1 radius := by
    unfold radiusL1
    positivity
  have hafterFirstRate0 : 0 ≤ afterFirstRate :=
    sharpAfterFirstPicardHistoryL1Rate_nonneg
      m kappa beta g hradius0 hactualBound0 hdefectRate0 hT
  have hfree := modalAbsSum_freeWeightedConfiguration_le
    radius (modeFrequency m) time phase
  have hactual := actualHistoryL1_le_energyEnvelope
    m hmUpper0 hmassUpper hbeta p q time
      (hgauge time htime) (henergy time htime)
  have hdefect :=
    modalAbsSum_physlibModalHistoryDefect_le_sharpRate_mul_time
      m hmUpper0 hmassUpper hbeta p q hp hq hHamilton radius phase
        hinitial htime hgauge henergy hzeroHistory
  have hdefectWindow : modalAbsSum
      (physlibModalHistoryDefect m q radius phase time) ≤ defectRate * T :=
    hdefect.trans (mul_le_mul_of_nonneg_left htime.2 hdefectRate0)
  have hafterFirst :=
    modalAbsSum_afterFirstPicardRemainder_le_sharpRate_mul_time
      m hmUpper0 hmassUpper hbeta p q hp hq hHamilton radius phase
        hinitial hT htime hgauge henergy hzeroHistory
  have hafterFirstWindow : modalAbsSum
      (physlibModalHistoryAfterFirstPicardRemainder
        m kappa g q radius phase time) ≤ afterFirstRate * T :=
    hafterFirst.trans
      (mul_le_mul_of_nonneg_left htime.2 hafterFirstRate0)
  have hlinear := norm_quadraticLinearHistoryRemainder_le_of_l1_bounds
    m kappa g observed q radius phase time homega hradius0 hfree
      hafterFirstWindow
  have hsquare := norm_quadraticDefectSquare_le_of_l1_bound
    m kappa g observed q radius phase time homega hdefectWindow
  have hcubic := norm_cubicHistoryRemainder_le_lipschitz_l1_bounds
    m beta g observed q radius phase time homega hactual hfree hdefectWindow
  unfold physlibFPUTAfterSecondPicardRemainderRotatedSource
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
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤
      (|kappa| * |g| *
        (2 * observedInteractionTensorAbsMass (n := 2) m observed *
          radiusL1 radius * (afterFirstRate * T))) /
          Real.sqrt (2 * modeFrequency m observed) +
      (|kappa| * |g| *
        (observedInteractionTensorAbsMass (n := 2) m observed *
          (defectRate * T) ^ 2)) /
          Real.sqrt (2 * modeFrequency m observed) +
      (|beta| * g ^ 2 *
        (observedInteractionTensorAbsMass (n := 3) m observed *
          ((defectRate * T) *
            (actualBound ^ 2 + actualBound * radiusL1 radius +
              radiusL1 radius ^ 2)))) /
          Real.sqrt (2 * modeFrequency m observed) :=
      add_le_add (add_le_add hlinear hsquare) hcubic
    _ = cubicLipschitzAfterSecondPicardSourceWindowEnvelope
        m kappa beta g observed (radiusL1 radius)
          (actualModalEnergyL1Envelope N mUpper kappa beta H)
          (sharpHistoryDefectL1Rate m kappa beta g
            (actualModalEnergyL1Envelope N mUpper kappa beta H))
          (sharpAfterFirstPicardHistoryL1Rate
            m kappa beta g (radiusL1 radius)
              (actualModalEnergyL1Envelope N mUpper kappa beta H)
              (sharpHistoryDefectL1Rate m kappa beta g
                (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) T := by
      dsimp only [actualBound, defectRate, afterFirstRate]
      unfold cubicLipschitzAfterSecondPicardSourceWindowEnvelope
      ring

/-- Integrated energy-window envelope for the cubic-Lipschitz post-second-
Picard coefficient. -/
def cubicLipschitzAfterSecondPicardCoefficientEnergyWindowEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  cubicLipschitzAfterSecondPicardSourceWindowEnvelope
      m kappa beta g observed (radiusL1 radius)
        (actualModalEnergyL1Envelope N mUpper kappa beta H)
        (sharpHistoryDefectL1Rate m kappa beta g
          (actualModalEnergyL1Envelope N mUpper kappa beta H))
        (sharpAfterFirstPicardHistoryL1Rate
          m kappa beta g (radiusL1 radius)
            (actualModalEnergyL1Envelope N mUpper kappa beta H)
            (sharpHistoryDefectL1Rate m kappa beta g
              (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) T * T

/-- Coefficient-level bound after integrating the improved pointwise source
over one nonnegative short block. -/
theorem norm_afterSecondPicardRemainderCoefficient_le_cubicLipschitzEnergyWindow
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
    (hinitial : ∀ mode,
      physlibModeAmplitude m mode p q 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize q) s) i = 0)
    (henergy : ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) s))
        (asConfiguration ((realReparametrize q) s)) ≤ H)
    (hzeroHistory : ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect m q radius phase s mode = 0) :
    ‖physlibFPUTAfterSecondPicardRemainderCoefficient
        m kappa beta g observed q radius phase T‖ ≤
      cubicLipschitzAfterSecondPicardCoefficientEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed := by
  unfold physlibFPUTAfterSecondPicardRemainderCoefficient
    cubicLipschitzAfterSecondPicardCoefficientEnergyWindowEnvelope
  calc
    ‖∫ time in (0 : Real)..T,
        physlibFPUTAfterSecondPicardRemainderRotatedSource
          m kappa beta g observed q radius phase time‖ ≤
      cubicLipschitzAfterSecondPicardSourceWindowEnvelope
          m kappa beta g observed (radiusL1 radius)
            (actualModalEnergyL1Envelope N mUpper kappa beta H)
            (sharpHistoryDefectL1Rate m kappa beta g
              (actualModalEnergyL1Envelope N mUpper kappa beta H))
            (sharpAfterFirstPicardHistoryL1Rate
              m kappa beta g (radiusL1 radius)
                (actualModalEnergyL1Envelope N mUpper kappa beta H)
                (sharpHistoryDefectL1Rate m kappa beta g
                  (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) T *
        |T - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro time htime
      have htimeIcc : time ∈ Icc 0 T := by
        simpa only [uIcc_of_le hT] using Set.uIoc_subset_uIcc htime
      exact
        norm_afterSecondPicardRemainderRotatedSource_le_cubicLipschitzWindow
          m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton
            radius phase hinitial homega hT htimeIcc hgauge henergy
              hzeroHistory
    _ = _ := by rw [sub_zero, abs_of_nonneg hT]

/-- Haar energy-correction envelope induced by the cubic-Lipschitz
coefficient bound. -/
def physlibHaarCubicLipschitzEnergyCorrectionEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  2 * finiteCharacterTwoStepAbsMass g
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
      (physlibQuadraticFirstPicardCharacterCoefficient
        m kappa radius T observed)
      (completeSecondPicardCoefficient m kappa beta radius observed T) *
      cubicLipschitzAfterSecondPicardCoefficientEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed +
    cubicLipschitzAfterSecondPicardCoefficientEnergyWindowEnvelope
      m mUpper kappa beta g H radius T observed ^ 2

/-- Actual one-block Haar energy drift with the cubic history difference
controlled by the true modal-history defect. -/
theorem abs_integral_actualPhaseModalNormSq_sub_initial_le_cubicLipschitzEnergyWindow
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (radius : Lattice.Site N → Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase mode,
      physlibModeAmplitude m mode (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (hT : 0 ≤ T)
    (hgauge : ∀ phase, ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) s) i = 0)
    (henergy : ∀ phase, ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) s))
        (asConfiguration ((realReparametrize (q phase)) s)) ≤ H)
    (hzeroHistory : ∀ phase, ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect
          m (q phase) radius phase s mode = 0)
    (hmeasurable : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius T)) :
    |(∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q T phase
        ∂finitePhaseHaarLaw (Lattice.Site N)) -
      ∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q 0 phase
        ∂finitePhaseHaarLaw (Lattice.Site N)| ≤
      g ^ 2 *
        (physlibHaarEnergyDriftC2 m kappa beta radius T observed +
          |g| * physlibHaarEnergyDriftC3 m kappa beta radius T observed +
          g ^ 2 * physlibHaarEnergyDriftC4
            m kappa beta radius T observed) +
        physlibHaarCubicLipschitzEnergyCorrectionEnvelope
          m mUpper kappa beta g H radius T observed := by
  apply abs_integral_actualPhaseModalNormSq_sub_initial_le_of_correction_bound
    m kappa beta g observed p q hp hq hHamilton radius homega
      (fun phase ↦ hinitial phase observed) T
      (physlibHaarCubicLipschitzEnergyCorrectionEnvelope
        m mUpper kappa beta g H radius T observed) hmeasurable
  intro phase
  apply abs_actualPostSecondPicardEnergyCorrection_le
    m kappa beta g observed q radius T phase homega
  exact
    norm_afterSecondPicardRemainderCoefficient_le_cubicLipschitzEnergyWindow
      m hmUpper0 hmassUpper hbeta observed (p phase) (q phase)
        (hp phase) (hq phase) (hHamilton phase) radius phase
          (hinitial phase) homega hT (hgauge phase) (henergy phase)
            (hzeroHistory phase)

/-! ## Exact extraction of the additional coupling power -/

/-- First-Duhamel source envelope after extracting its leading `|g|`. -/
def firstDuhamelWindowUnitCouplingEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N) (actualBound : Real) : Real :=
  ((|kappa| *
      observedInteractionTensorAbsMass (n := 2) m observed *
        actualBound ^ 2) +
    (|beta| * |g| *
      observedInteractionTensorAbsMass (n := 3) m observed *
        actualBound ^ 3)) /
    Real.sqrt (2 * modeFrequency m observed)

theorem firstDuhamelWindowEnvelope_eq_abs_mul_unitCoupling
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N) (actualBound : Real) :
    firstDuhamelWindowEnvelope m kappa beta g observed actualBound =
      |g| * firstDuhamelWindowUnitCouplingEnvelope
        m kappa beta g observed actualBound := by
  unfold firstDuhamelWindowEnvelope
    firstDuhamelWindowUnitCouplingEnvelope
  rw [← sq_abs g]
  ring

/-- Modal `l1` history-defect rate after extracting its exact leading
`|g|`. -/
def sharpHistoryDefectL1UnitRate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g actualBound : Real) :
    Real :=
  ∑ mode, positiveModeCoordinateRecoveryFactor m mode *
    firstDuhamelWindowUnitCouplingEnvelope
      m kappa beta g mode actualBound

theorem sharpHistoryDefectL1Rate_eq_abs_mul_unitRate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g actualBound : Real) :
    sharpHistoryDefectL1Rate m kappa beta g actualBound =
      |g| * sharpHistoryDefectL1UnitRate
        m kappa beta g actualBound := by
  classical
  unfold sharpHistoryDefectL1Rate sharpHistoryDefectL1UnitRate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mode hmode
  rw [firstDuhamelWindowEnvelope_eq_abs_mul_unitCoupling]
  ring

/-- After-first-Picard source envelope after extracting the exact factor
`|g|^2`, assuming the supplied defect rate was written as
`|g| * defectUnit`. -/
def sharpFirstPicardRemainderSourceWindowUnitEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (freeBound actualBound defectUnit T : Real) : Real :=
  ((|kappa| *
      (observedInteractionTensorAbsMass (n := 2) m observed *
        (2 * freeBound * (defectUnit * T) +
          |g| * (defectUnit * T) ^ 2))) +
    (|beta| *
      (observedInteractionTensorAbsMass (n := 3) m observed *
        actualBound ^ 3))) /
    Real.sqrt (2 * modeFrequency m observed)

theorem sharpFirstPicardRemainderSourceWindowEnvelope_abs_factor
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (freeBound actualBound defectUnit T : Real) :
    sharpFirstPicardRemainderSourceWindowEnvelope
        m kappa beta g observed freeBound actualBound
          (|g| * defectUnit) T =
      |g| ^ 2 * sharpFirstPicardRemainderSourceWindowUnitEnvelope
        m kappa beta g observed freeBound actualBound defectUnit T := by
  unfold sharpFirstPicardRemainderSourceWindowEnvelope
    sharpFirstPicardRemainderSourceWindowUnitEnvelope
  rw [← sq_abs g]
  ring

/-- Finite modal `l1` after-first-Picard rate with the exact `|g|^2`
factor removed. -/
def sharpAfterFirstPicardHistoryL1UnitRate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (freeBound actualBound defectUnit T : Real) : Real :=
  ∑ mode, positiveModeCoordinateRecoveryFactor m mode *
    sharpFirstPicardRemainderSourceWindowUnitEnvelope
      m kappa beta g mode freeBound actualBound defectUnit T

theorem sharpAfterFirstPicardHistoryL1Rate_abs_factor
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (freeBound actualBound defectUnit T : Real) :
    sharpAfterFirstPicardHistoryL1Rate
        m kappa beta g freeBound actualBound (|g| * defectUnit) T =
      |g| ^ 2 * sharpAfterFirstPicardHistoryL1UnitRate
        m kappa beta g freeBound actualBound defectUnit T := by
  classical
  unfold sharpAfterFirstPicardHistoryL1Rate
    sharpAfterFirstPicardHistoryL1UnitRate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mode hmode
  rw [sharpFirstPicardRemainderSourceWindowEnvelope_abs_factor]
  ring

/-- Cubic-Lipschitz post-second-Picard source after extracting `|g|^3`.
All remaining quantities are finite-volume short-block constants. -/
def cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (observed : Lattice.Site N)
    (freeBound actualBound defectUnit afterFirstUnit T : Real) : Real :=
  ((|kappa| *
      (2 * observedInteractionTensorAbsMass (n := 2) m observed *
        freeBound * (afterFirstUnit * T))) +
    (|kappa| *
      (observedInteractionTensorAbsMass (n := 2) m observed *
        (defectUnit * T) ^ 2)) +
    (|beta| *
      (observedInteractionTensorAbsMass (n := 3) m observed *
        ((defectUnit * T) *
          (actualBound ^ 2 + actualBound * freeBound + freeBound ^ 2))))) /
    Real.sqrt (2 * modeFrequency m observed)

theorem cubicLipschitzAfterSecondPicardSourceWindowEnvelope_abs_cube_factor
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (freeBound actualBound defectUnit afterFirstUnit T : Real) :
    cubicLipschitzAfterSecondPicardSourceWindowEnvelope
        m kappa beta g observed freeBound actualBound
          (|g| * defectUnit) (|g| ^ 2 * afterFirstUnit) T =
      |g| ^ 3 * cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
        m kappa beta observed freeBound actualBound
          defectUnit afterFirstUnit T := by
  unfold cubicLipschitzAfterSecondPicardSourceWindowEnvelope
    cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
  rw [← sq_abs g]
  ring

/-- Energy-window unit source envelope.  Multiplying this quantity by
`|g|^3` recovers the complete improved source envelope. -/
def cubicLipschitzAfterSecondPicardSourceUnitEnergyWindowEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  cubicLipschitzAfterSecondPicardSourceWindowUnitEnvelope
    m kappa beta observed (radiusL1 radius)
      (actualModalEnergyL1Envelope N mUpper kappa beta H)
      (sharpHistoryDefectL1UnitRate m kappa beta g
        (actualModalEnergyL1Envelope N mUpper kappa beta H))
      (sharpAfterFirstPicardHistoryL1UnitRate
        m kappa beta g (radiusL1 radius)
          (actualModalEnergyL1Envelope N mUpper kappa beta H)
          (sharpHistoryDefectL1UnitRate m kappa beta g
            (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) T

/-- Exact `|g|^3` factorization of the improved energy-window source. -/
theorem cubicLipschitzAfterSecondPicardSourceEnergyWindow_abs_cube_factor
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) :
    cubicLipschitzAfterSecondPicardSourceWindowEnvelope
        m kappa beta g observed (radiusL1 radius)
          (actualModalEnergyL1Envelope N mUpper kappa beta H)
          (sharpHistoryDefectL1Rate m kappa beta g
            (actualModalEnergyL1Envelope N mUpper kappa beta H))
          (sharpAfterFirstPicardHistoryL1Rate
            m kappa beta g (radiusL1 radius)
              (actualModalEnergyL1Envelope N mUpper kappa beta H)
              (sharpHistoryDefectL1Rate m kappa beta g
                (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) T =
      |g| ^ 3 *
        cubicLipschitzAfterSecondPicardSourceUnitEnergyWindowEnvelope
          m mUpper kappa beta g H radius T observed := by
  rw [sharpHistoryDefectL1Rate_eq_abs_mul_unitRate]
  rw [sharpAfterFirstPicardHistoryL1Rate_abs_factor]
  unfold cubicLipschitzAfterSecondPicardSourceUnitEnergyWindowEnvelope
  exact
    cubicLipschitzAfterSecondPicardSourceWindowEnvelope_abs_cube_factor
      m kappa beta g observed (radiusL1 radius)
        (actualModalEnergyL1Envelope N mUpper kappa beta H)
        (sharpHistoryDefectL1UnitRate m kappa beta g
          (actualModalEnergyL1Envelope N mUpper kappa beta H))
        (sharpAfterFirstPicardHistoryL1UnitRate
          m kappa beta g (radiusL1 radius)
            (actualModalEnergyL1Envelope N mUpper kappa beta H)
            (sharpHistoryDefectL1UnitRate m kappa beta g
              (actualModalEnergyL1Envelope N mUpper kappa beta H)) T) T

/-- Unit coefficient envelope after extracting the exact `|g|^3`. -/
def cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  cubicLipschitzAfterSecondPicardSourceUnitEnergyWindowEnvelope
    m mUpper kappa beta g H radius T observed * T

/-- The complete integrated remainder coefficient is exactly bounded by an
envelope carrying `|g|^3`; no hidden order-`g^2` cubic-history term remains. -/
theorem cubicLipschitzAfterSecondPicardCoefficientEnvelope_abs_cube_factor
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) :
    cubicLipschitzAfterSecondPicardCoefficientEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed =
      |g| ^ 3 *
        cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
          m mUpper kappa beta g H radius T observed := by
  unfold cubicLipschitzAfterSecondPicardCoefficientEnergyWindowEnvelope
    cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
  rw [cubicLipschitzAfterSecondPicardSourceEnergyWindow_abs_cube_factor]
  ring

/-- Unit Haar correction after extracting the common leading `|g|^3`.
The square of the remainder contributes the displayed additional
`|g|^3` inside this unit envelope. -/
def physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  2 * finiteCharacterTwoStepAbsMass g
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
      (physlibQuadraticFirstPicardCharacterCoefficient
        m kappa radius T observed)
      (completeSecondPicardCoefficient m kappa beta radius observed T) *
      cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed +
    |g| ^ 3 *
      cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed ^ 2

/-- Exact `|g|^3` factorization of the nonlinear Haar energy correction. -/
theorem physlibHaarCubicLipschitzEnergyCorrectionEnvelope_abs_cube_factor
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real)
    (radius : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) :
    physlibHaarCubicLipschitzEnergyCorrectionEnvelope
        m mUpper kappa beta g H radius T observed =
      |g| ^ 3 *
        physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
          m mUpper kappa beta g H radius T observed := by
  unfold physlibHaarCubicLipschitzEnergyCorrectionEnvelope
    physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
  rw [cubicLipschitzAfterSecondPicardCoefficientEnvelope_abs_cube_factor]
  ring

/-- Consumer-ready coefficient estimate with the additional coupling power
displayed explicitly. -/
theorem norm_afterSecondPicardRemainderCoefficient_le_abs_cube_mul_unit
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
    (hinitial : ∀ mode,
      physlibModeAmplitude m mode p q 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (homega : 0 < modeFrequency m observed)
    (hT : 0 ≤ T)
    (hgauge : ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize q) s) i = 0)
    (henergy : ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize p) s))
        (asConfiguration ((realReparametrize q) s)) ≤ H)
    (hzeroHistory : ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect m q radius phase s mode = 0) :
    ‖physlibFPUTAfterSecondPicardRemainderCoefficient
        m kappa beta g observed q radius phase T‖ ≤
      |g| ^ 3 *
        cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
          m mUpper kappa beta g H radius T observed := by
  rw [← cubicLipschitzAfterSecondPicardCoefficientEnvelope_abs_cube_factor]
  exact
    norm_afterSecondPicardRemainderCoefficient_le_cubicLipschitzEnergyWindow
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius phase
        hinitial homega hT hgauge henergy hzeroHistory

/-- Haar energy drift with the nonlinear correction displayed as a genuine
`|g|^3` short-block remainder. -/
theorem abs_integral_actualPhaseModalNormSq_sub_initial_le_abs_cube_correction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (radius : Lattice.Site N → Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : ∀ phase mode,
      physlibModeAmplitude m mode (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (hT : 0 ≤ T)
    (hgauge : ∀ phase, ∀ s ∈ Icc 0 T, ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) s) i = 0)
    (henergy : ∀ phase, ∀ s ∈ Icc 0 T,
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) s))
        (asConfiguration ((realReparametrize (q phase)) s)) ≤ H)
    (hzeroHistory : ∀ phase, ∀ s ∈ Icc 0 T, ∀ mode,
      modeFrequency m mode = 0 →
        physlibModalHistoryDefect
          m (q phase) radius phase s mode = 0)
    (hmeasurable : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius T)) :
    |(∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q T phase
        ∂finitePhaseHaarLaw (Lattice.Site N)) -
      ∫ phase : UnitAddTorus (Lattice.Site N),
        actualPhaseModalNormSq m observed p q 0 phase
        ∂finitePhaseHaarLaw (Lattice.Site N)| ≤
      g ^ 2 *
        (physlibHaarEnergyDriftC2 m kappa beta radius T observed +
          |g| * physlibHaarEnergyDriftC3 m kappa beta radius T observed +
          g ^ 2 * physlibHaarEnergyDriftC4
            m kappa beta radius T observed) +
        |g| ^ 3 *
          physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
            m mUpper kappa beta g H radius T observed := by
  rw [← physlibHaarCubicLipschitzEnergyCorrectionEnvelope_abs_cube_factor]
  exact
    abs_integral_actualPhaseModalNormSq_sub_initial_le_cubicLipschitzEnergyWindow
      m hmUpper0 hmassUpper hbeta observed p q hp hq hHamilton radius homega
        hinitial hT hgauge henergy hzeroHistory hmeasurable

end

end ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
