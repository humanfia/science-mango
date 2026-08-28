import ArchonPhysics.CanonicalFixedRadiusHaarMomentClosure

/-!
# Actual Physlib one-block fixed-radius Haar closure

This module applies the exact charge-balanced fixed-radius Haar moments to a
finite family of positive modes evolved by the genuine Physlib Hamiltonian.
The deterministic first-Duhamel estimate supplies the pointwise coupling to
the canonical initial Haar family.  Consequently every normal two-point and
four-point phase average has the correct non-Gaussian charge target, with the
explicit `2 M epsilon` and `4 M^3 epsilon` errors.

This is one nonlinear time block.  It does not assume an independent fresh
Haar restart, but it also does not propagate the estimate through kinetic
time.
-/

namespace ArchonPhysics.PhyslibFPUTActualFixedRadiusHaarMomentClosure

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalFixedRadiusHaarMomentClosure
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.Lattice
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTFirstDuhamelEnergyWindow
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- A genuine Hamiltonian block which is uniformly controlled by its
first-Duhamel error satisfies the exact fixed-radius, charge-balanced RPA
closure simultaneously for every selected positive mode. -/
theorem actual_physlib_shortTime_chargeBalanced_two_and_four_moments
    {I : Type*} {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H T M epsilon : Real}
    (hmUpper0 : 0 ≤ mUpper) (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (selected : I → Site N)
    (p q : UnitAddTorus (Site N) → Time → HilbertConfiguration N)
    (hp : ∀ phase, Differentiable Real (p phase))
    (hq : ∀ phase, Differentiable Real (q phase))
    (hHamilton : ∀ phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (hpositive : ∀ a, 0 < modeFrequency m (selected a))
    (hT : 0 ≤ T)
    (hgauge : ∀ phase time, time ∈ Set.Icc 0 T →
      ∑ i, m.mass i *
        asConfiguration ((realReparametrize (q phase)) time) i = 0)
    (henergy : ∀ phase time, time ∈ Set.Icc 0 T →
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) time))
        (asConfiguration ((realReparametrize (q phase)) time)) ≤ H)
    (radius : Site N → Real)
    (hinitial : ∀ phase a,
      physlibModeAmplitude m (selected a) (p phase) (q phase) 0 =
        ArchonPhysics.FreeFPUTA0DirectCubicBridge.canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase (selected a))
    (hactualMeasurable : ∀ a, Measurable
      (fun phase : UnitAddTorus (Site N) ↦
        physlibModeAmplitude m (selected a) (p phase) (q phase) T))
    (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hactualBound : ∀ phase a,
      ‖actualInteractionPictureHaarAmplitude
        m (selected a) p q T phase‖ ≤ M)
    (hinitialBound : ∀ a,
      canonicalHaarInitialMagnitude radius (modeFrequency m) (selected a) ≤ M)
    (herror : ∀ a,
      shortTimeRPABlockError
        m mUpper kappa beta g H (selected a) T ≤ epsilon) :
    (∀ i j : I,
      ‖(∫ phase : UnitAddTorus (Site N),
          twoPointProduct
            (actualInteractionPictureHaarAmplitude
              m (selected i) p q T phase)
            (actualInteractionPictureHaarAmplitude
              m (selected j) p q T phase)
          ∂finitePhaseHaarLaw (Site N)) -
        (if canonicalInitialHaarCharge (selected i) -
              canonicalInitialHaarCharge (selected j) = 0 then
          canonicalInitialHaarCoefficient radius (modeFrequency m) (selected i) *
            starRingEnd Complex
              (canonicalInitialHaarCoefficient
                radius (modeFrequency m) (selected j)) else 0)‖ ≤
        2 * M * epsilon) ∧
    (∀ i j k l : I,
      ‖(∫ phase : UnitAddTorus (Site N),
          fourPointProduct
            (actualInteractionPictureHaarAmplitude
              m (selected i) p q T phase)
            (actualInteractionPictureHaarAmplitude
              m (selected j) p q T phase)
            (actualInteractionPictureHaarAmplitude
              m (selected k) p q T phase)
            (actualInteractionPictureHaarAmplitude
              m (selected l) p q T phase)
          ∂finitePhaseHaarLaw (Site N)) -
        (if (canonicalInitialHaarCharge (selected i) -
                canonicalInitialHaarCharge (selected j)) +
              (canonicalInitialHaarCharge (selected k) -
                canonicalInitialHaarCharge (selected l)) = 0 then
          (canonicalInitialHaarCoefficient
              radius (modeFrequency m) (selected i) *
            starRingEnd Complex
              (canonicalInitialHaarCoefficient
                radius (modeFrequency m) (selected j))) *
          (canonicalInitialHaarCoefficient
              radius (modeFrequency m) (selected k) *
            starRingEnd Complex
              (canonicalInitialHaarCoefficient
                radius (modeFrequency m) (selected l))) else 0)‖ ≤
        4 * M ^ 3 * epsilon) := by
  let coefficient : I → Complex := fun a ↦
    canonicalInitialHaarCoefficient radius (modeFrequency m) (selected a)
  let charge : I → Site N → Int := fun a ↦
    canonicalInitialHaarCharge (selected a)
  let actual : UnitAddTorus (Site N) → I → Complex := fun phase a ↦
    actualInteractionPictureHaarAmplitude m (selected a) p q T phase
  have hactualMeasurable' : ∀ a,
      Measurable (fun phase : UnitAddTorus (Site N) ↦ actual phase a) := by
    intro a
    exact measurable_actualInteractionPictureHaarAmplitude
      m (selected a) p q T (hactualMeasurable a)
  have hrefEq : ∀ phase a,
      fixedRadiusHaarAmplitude coefficient charge phase a =
        ArchonPhysics.FreeFPUTA0DirectCubicBridge.canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase (selected a) := by
    intro phase a
    dsimp [fixedRadiusHaarAmplitude, coefficient, charge,
      canonicalInitialHaarCoefficient, canonicalInitialHaarCharge]
    rw [mFourier_freeInitialPhaseCharge]
    exact
      (canonicalFreeComplexInitialAmplitude_eq_coefficient_mul_unitPhase
        radius (modeFrequency m) phase (selected a)).symm
  have hrefBound : ∀ a, ‖coefficient a‖ ≤ M := by
    intro a
    calc
      ‖coefficient a‖ =
          ‖fixedRadiusHaarAmplitude coefficient charge
            (0 : UnitAddTorus (Site N)) a‖ :=
        (norm_fixedRadiusHaarAmplitude coefficient charge 0 a).symm
      _ = ‖ArchonPhysics.FreeFPUTA0DirectCubicBridge.canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) 0 (selected a)‖ := by rw [hrefEq]
      _ = canonicalHaarInitialMagnitude
          radius (modeFrequency m) (selected a) :=
        norm_canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) 0 (selected a)
      _ ≤ M := hinitialBound a
  have hdistance : ∀ phase a,
      ‖actual phase a -
        fixedRadiusHaarAmplitude coefficient charge phase a‖ ≤ epsilon := by
    intro phase a
    rw [hrefEq phase a]
    exact (norm_actualInteractionPictureHaarAmplitude_sub_initial_le
      m hmUpper0 hmassUpper hbeta (selected a) p q hp hq hHamilton
        (hpositive a) hT hgauge henergy radius (fun phase ↦ hinitial phase a)
        phase).trans (herror a)
  constructor
  · intro i j
    simpa [actual, coefficient, charge] using
      (norm_integral_twoPoint_sub_chargeBalanced_le
        coefficient charge actual hactualMeasurable' hM hepsilon
        hactualBound hrefBound hdistance i j)
  · intro i j k l
    simpa [actual, coefficient, charge] using
      (norm_integral_fourPoint_sub_chargeBalanced_le
        coefficient charge actual hactualMeasurable' hM hepsilon
        hactualBound hrefBound hdistance i j k l)

end

end ArchonPhysics.PhyslibFPUTActualFixedRadiusHaarMomentClosure
