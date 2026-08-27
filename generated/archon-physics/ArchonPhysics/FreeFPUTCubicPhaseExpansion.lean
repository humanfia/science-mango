import ArchonPhysics.FreeFPUTMismatchPhaseExpansion
import ArchonPhysics.FiniteHaarOscillatorySecondMoment
import ArchonPhysics.ForcedComplexModeDuhamel

/-!
# Free cubic FPUT sources as finite phase-character families

This module gives the exact finite-volume character expansion of the cubic
modal force evaluated on the freely rotating real modal configuration.  A
term records three internal modes and one of the two real-part signs on each
leg.  Its output-rotated time phase is the output frequency minus the
charge-weighted input frequency, and its finite-time integral is expressed by
the existing `oscillatoryCoefficient` family.

These are algebraic free-orbit and finite-interval identities.  They do not
assert random-phase propagation, a kinetic limit, or equilibration.
-/

namespace ArchonPhysics.FreeFPUTCubicPhaseExpansion

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModeCoupling
open ArchonPhysics.PhaseRenormalization

open scoped Interval

noncomputable section

/-- One cubic tensor term consists of three internal modes and one signed
real-part sector on each input leg. -/
abbrev CubicPhaseTerm (N : Nat) :=
  (Fin 3 → Lattice.Site N) × (Fin 3 → Fin 2)

/-- Total Haar charge carried by the three signed input legs. -/
def cubicPhaseCharge {N : Nat} [NeZero N]
    (term : CubicPhaseTerm N) : Lattice.Site N → Int :=
  (binarySignedMode (term.1 0) (term.2 0)).charge +
    (binarySignedMode (term.1 1) (term.2 1)).charge +
    (binarySignedMode (term.1 2) (term.2 2)).charge

/-- Deterministic coefficient of one signed cubic tensor character. -/
def cubicPhaseCoefficient {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (term : CubicPhaseTerm N) : Complex :=
  (interactionTensor m 4 (Fin.cons observed term.1) : Complex) *
    ((radius (term.1 0) / 2 : Real) : Complex) *
    ((radius (term.1 1) / 2 : Real) : Complex) *
    ((radius (term.1 2) / 2 : Real) : Complex)

/-- Finite character polynomial representing the cubic tensor source. -/
def cubicTensorPhasePolynomial {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  finitePhaseCorrection
    (cubicPhaseCoefficient m observed radius) cubicPhaseCharge phase

/-- Complexification of the cubic tensor contraction evaluated on the free
real modal orbit. -/
def freeCubicTensorSource {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  ∑ modes : Fin 3 → Lattice.Site N,
    (interactionTensor m 4 (Fin.cons observed modes) : Complex) *
      ∏ r, (freeRealModeCoordinate radius frequency time phase (modes r) : Complex)

/-- The explicit cubic source is exactly the complexification of the existing
`distinguishedTensorContraction` at input order three. -/
theorem freeCubicTensorSource_eq_complex_tensorContraction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeCubicTensorSource m observed radius frequency time phase =
      (distinguishedTensorContraction m
        (freeWeightedConfiguration radius frequency time phase) observed 3 : Real) := by
  unfold freeCubicTensorSource distinguishedTensorContraction
  push_cast
  rfl

/-- The product of three signed single-mode factors is the multivariate
character of their total charge. -/
theorem prod_three_binarySignedCharacter_eq_mFourier
    {d : Type*} [Fintype d] [DecidableEq d]
    (modes : Fin 3 → d) (signs : Fin 3 → Fin 2)
    (phase : UnitAddTorus d) :
    (∏ r, binarySignedCharacter (modes r) (signs r) phase) =
      mFourier
        ((binarySignedMode (modes 0) (signs 0)).charge +
          (binarySignedMode (modes 1) (signs 1)).charge +
          (binarySignedMode (modes 2) (signs 2)).charge) phase := by
  rw [Fin.prod_univ_three]
  unfold binarySignedCharacter
  rw [SignedMode.phaseFactor_eq_mFourier,
    SignedMode.phaseFactor_eq_mFourier,
    SignedMode.phaseFactor_eq_mFourier,
    ← mFourier_add, ← mFourier_add]

/-- Exact finite-character expansion of the free cubic (four-leg) tensor
source. -/
theorem freeCubicTensorSource_eq_phasePolynomial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeCubicTensorSource m observed radius frequency time phase =
      cubicTensorPhasePolynomial m observed radius
        (physicalFreePhaseEvolution frequency time phase) := by
  classical
  unfold freeCubicTensorSource cubicTensorPhasePolynomial
    finitePhaseCorrection
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro modes hmodes
  simp_rw [coe_freeRealModeCoordinate_eq_binarySignedSum]
  rw [Fintype.prod_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro signs hsigns
  simp only [cubicPhaseCoefficient, cubicPhaseCharge]
  have hcharacter := prod_three_binarySignedCharacter_eq_mFourier
    modes signs (physicalFreePhaseEvolution frequency time phase)
  rw [Fin.prod_univ_three] at hcharacter
  rw [Fin.prod_univ_three, ← hcharacter]
  ring

/-- A deterministic scalar multiple of the free cubic tensor source. -/
def freeCubicPicardIntegrand {N : Nat} [NeZero N]
    (timeCoefficient : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  timeCoefficient *
    freeCubicTensorSource m observed radius frequency time phase

/-- Time-independent coefficient before the output phase and mismatch
oscillation are inserted. -/
def cubicDuhamelCoefficient {N : Nat} [NeZero N]
    (coupling : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (term : CubicPhaseTerm N) : Complex :=
  coupling * cubicPhaseCoefficient m observed radius term

/-- Output-minus-input mismatch of a signed cubic source monomial. -/
def cubicPhaseMismatch {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : CubicPhaseTerm N) : Real :=
  outputChargeMismatch (frequency observed) (cubicPhaseCharge term) frequency

/-- Exact mismatch expansion after inserting a fixed coupling and the output
interaction-picture phase. -/
theorem freeCubicPicardIntegrand_eq_mismatchSum
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeCubicPicardIntegrand
        (coupling * phaseFactor (frequency observed * time))
        m observed radius frequency time phase =
      ∑ term : CubicPhaseTerm N,
        (cubicDuhamelCoefficient coupling m observed radius term *
          mFourier (cubicPhaseCharge term) phase) *
          Complex.exp
            ((Complex.I *
              (cubicPhaseMismatch frequency observed term : Real)) * time) := by
  classical
  unfold freeCubicPicardIntegrand
  rw [freeCubicTensorSource_eq_phasePolynomial]
  unfold cubicTensorPhasePolynomial finitePhaseCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro term hterm
  have hphase :=
    phaseFactor_mul_mFourier_physicalFreePhaseEvolution
      (frequency observed) (cubicPhaseCharge term) frequency time phase
  have hphaseMismatch :
      phaseFactor (frequency observed * time) *
          mFourier (cubicPhaseCharge term)
            (physicalFreePhaseEvolution frequency time phase) =
        Complex.exp
            ((Complex.I *
              (cubicPhaseMismatch frequency observed term : Real)) * time) *
          mFourier (cubicPhaseCharge term) phase := by
    simpa only [cubicPhaseMismatch] using hphase
  rw [show
    (coupling * phaseFactor (frequency observed * time)) *
        (cubicPhaseCoefficient m observed radius term *
          mFourier (cubicPhaseCharge term)
            (physicalFreePhaseEvolution frequency time phase)) =
      (coupling * cubicPhaseCoefficient m observed radius term) *
        (phaseFactor (frequency observed * time) *
          mFourier (cubicPhaseCharge term)
            (physicalFreePhaseEvolution frequency time phase)) by ring]
  rw [hphaseMismatch]
  unfold cubicDuhamelCoefficient
  ring

/-- The complex coefficient multiplying a unit free cubic tensor contraction
in the forced positive-frequency mode equation.  The real force coefficient
is `-beta`, as in the FPUT quartic force. -/
def physicalCubicUnitCoupling (outputFrequency beta : Real) : Complex :=
  forcedModeSource outputFrequency (-beta)

/-- The output-rotated physical cubic force evaluated on the free modal
configuration. -/
def physicalFreeCubicPicardIntegrand {N : Nat} [NeZero N]
    (beta : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  phaseFactor (frequency observed * time) *
    forcedModeSource (frequency observed)
      (-(beta * distinguishedTensorContraction m
        (freeWeightedConfiguration radius frequency time phase) observed 3))

/-- The physical cubic integrand is the generic character integrand with the
forced-mode unit coupling. -/
theorem physicalFreeCubicPicardIntegrand_eq_freeCubicPicardIntegrand
    {N : Nat} [NeZero N]
    (beta : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    physicalFreeCubicPicardIntegrand beta m observed radius frequency time phase =
      freeCubicPicardIntegrand
        (physicalCubicUnitCoupling (frequency observed) beta *
          phaseFactor (frequency observed * time))
        m observed radius frequency time phase := by
  unfold physicalFreeCubicPicardIntegrand freeCubicPicardIntegrand
  rw [freeCubicTensorSource_eq_complex_tensorContraction]
  unfold physicalCubicUnitCoupling forcedModeSource
  push_cast
  ring

/-- Exact physical mismatch expansion, with the output phase and the FPUT
cubic unit coupling displayed in the coefficient family. -/
theorem physicalFreeCubicPicardIntegrand_eq_mismatchSum
    {N : Nat} [NeZero N]
    (beta : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    physicalFreeCubicPicardIntegrand beta m observed radius frequency time phase =
      ∑ term : CubicPhaseTerm N,
        (cubicDuhamelCoefficient
            (physicalCubicUnitCoupling (frequency observed) beta)
            m observed radius term *
          mFourier (cubicPhaseCharge term) phase) *
          Complex.exp
            ((Complex.I *
              (cubicPhaseMismatch frequency observed term : Real)) * time) := by
  rw [physicalFreeCubicPicardIntegrand_eq_freeCubicPicardIntegrand]
  exact freeCubicPicardIntegrand_eq_mismatchSum
    (physicalCubicUnitCoupling (frequency observed) beta)
    m observed radius frequency time phase

/-- The finite-time integral of the generic cubic source is exactly the
existing finite oscillatory character family. -/
theorem intervalIntegral_freeCubicPicardIntegrand_eq_oscillatoryFamily
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    (∫ s in (0 : Real)..time,
      freeCubicPicardIntegrand
        (coupling * phaseFactor (frequency observed * s))
        m observed radius frequency s phase) =
      finiteHaarOscillatorySum
        (cubicDuhamelCoefficient coupling m observed radius)
        cubicPhaseCharge (cubicPhaseMismatch frequency observed)
        time phase := by
  classical
  calc
    (∫ s in (0 : Real)..time,
      freeCubicPicardIntegrand
        (coupling * phaseFactor (frequency observed * s))
        m observed radius frequency s phase) =
        ∫ s in (0 : Real)..time,
          ∑ term : CubicPhaseTerm N,
            (cubicDuhamelCoefficient coupling m observed radius term *
              mFourier (cubicPhaseCharge term) phase) *
              Complex.exp
                ((Complex.I *
                  (cubicPhaseMismatch frequency observed term : Real)) * s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact freeCubicPicardIntegrand_eq_mismatchSum
        coupling m observed radius frequency s phase
    _ = ∑ term : CubicPhaseTerm N,
        ∫ s in (0 : Real)..time,
          (cubicDuhamelCoefficient coupling m observed radius term *
            mFourier (cubicPhaseCharge term) phase) *
            Complex.exp
              ((Complex.I *
                (cubicPhaseMismatch frequency observed term : Real)) * s) := by
      apply intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume)
      intro term hterm
      exact Continuous.intervalIntegrable (μ := MeasureTheory.volume)
        (by fun_prop : Continuous (fun s : Real ↦
          (cubicDuhamelCoefficient coupling m observed radius term *
            mFourier (cubicPhaseCharge term) phase) *
            Complex.exp
              ((Complex.I *
                (cubicPhaseMismatch frequency observed term : Real)) * s)))
        0 time
    _ = finiteHaarOscillatorySum
        (cubicDuhamelCoefficient coupling m observed radius)
        cubicPhaseCharge (cubicPhaseMismatch frequency observed)
        time phase := by
      unfold finiteHaarOscillatorySum finitePhaseCorrection
        oscillatoryCoefficient
      apply Finset.sum_congr rfl
      intro term hterm
      rw [intervalIntegral_const_mul_mismatchExp]
      ring

/-- Physical specialization of the finite-time oscillatory family. -/
theorem intervalIntegral_physicalFreeCubicPicardIntegrand_eq_oscillatoryFamily
    {N : Nat} [NeZero N]
    (beta : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    (∫ s in (0 : Real)..time,
      physicalFreeCubicPicardIntegrand
        beta m observed radius frequency s phase) =
      finiteHaarOscillatorySum
        (cubicDuhamelCoefficient
          (physicalCubicUnitCoupling (frequency observed) beta)
          m observed radius)
        cubicPhaseCharge (cubicPhaseMismatch frequency observed)
        time phase := by
  calc
    (∫ s in (0 : Real)..time,
      physicalFreeCubicPicardIntegrand
        beta m observed radius frequency s phase) =
        ∫ s in (0 : Real)..time,
          freeCubicPicardIntegrand
            (physicalCubicUnitCoupling (frequency observed) beta *
              phaseFactor (frequency observed * s))
            m observed radius frequency s phase := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact physicalFreeCubicPicardIntegrand_eq_freeCubicPicardIntegrand
        beta m observed radius frequency s phase
    _ = finiteHaarOscillatorySum
        (cubicDuhamelCoefficient
          (physicalCubicUnitCoupling (frequency observed) beta)
          m observed radius)
        cubicPhaseCharge (cubicPhaseMismatch frequency observed)
        time phase :=
      intervalIntegral_freeCubicPicardIntegrand_eq_oscillatoryFamily
        (physicalCubicUnitCoupling (frequency observed) beta)
        m observed radius frequency time phase

end

end ArchonPhysics.FreeFPUTCubicPhaseExpansion
