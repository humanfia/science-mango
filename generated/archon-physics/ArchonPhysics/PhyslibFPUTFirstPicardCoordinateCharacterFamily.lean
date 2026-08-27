import ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

/-!
# Exact phase-character family for the real first-Picard coordinate

The quadratic Physlib/FPUT first Picard coefficient is first identified with
the existing finite oscillatory Haar sum indexed by `QuadraticPhaseTerm`.
Undoing the interaction-picture phase and taking the real coordinate then
duplicates each term into two literal branches: the original character and
its complex-conjugate character.  Their charges are respectively `q` and
`-q`, and both carry the exact factor

`(sqrt (2 * omega) / omega) / 2`.

The construction keeps every term of the finite family, including distinct
terms with the same charge.  At zero observed frequency it uses the already
proved tensor-decoupling theorem for the first Picard coefficient; zero is
not inferred by cancelling or dividing by the frequency.  These are exact
finite-volume identities only, with no collision or kinetic-limit claim.
-/

namespace ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open scoped ComplexConjugate

noncomputable section

/-! ## Generic real-part duplication for a finite character family -/

/-- The two coefficients obtained from taking the real part of a finite
character family.  Branch zero carries the supplied coefficient and branch
one its complex conjugate; the real-part factor `1 / 2` is explicit. -/
def twoBranchRealPartCoefficient
    {J : Type*} (scale : Real) (coefficient : J → Complex)
    (entry : J × Fin 2) : Complex :=
  (((scale / 2 : Real) : Complex) *
    if entry.2 = 0 then coefficient entry.1
    else starRingEnd Complex (coefficient entry.1))

/-- The original branch retains its charge and the conjugate branch carries
the negative charge. -/
def twoBranchRealPartCharge
    {d J : Type*} (charge : J → d → Int) (entry : J × Fin 2) : d → Int :=
  if entry.2 = 0 then charge entry.1 else -charge entry.1

@[simp] theorem twoBranchRealPartCoefficient_zero
    {J : Type*} (scale : Real) (coefficient : J → Complex) (term : J) :
    twoBranchRealPartCoefficient scale coefficient (term, 0) =
      (((scale / 2 : Real) : Complex) * coefficient term) := by
  simp [twoBranchRealPartCoefficient]

@[simp] theorem twoBranchRealPartCoefficient_one
    {J : Type*} (scale : Real) (coefficient : J → Complex) (term : J) :
    twoBranchRealPartCoefficient scale coefficient (term, 1) =
      (((scale / 2 : Real) : Complex) *
        starRingEnd Complex (coefficient term)) := by
  simp [twoBranchRealPartCoefficient]

@[simp] theorem twoBranchRealPartCharge_zero
    {d J : Type*} (charge : J → d → Int) (term : J) :
    twoBranchRealPartCharge charge (term, 0) = charge term := by
  simp [twoBranchRealPartCharge]

@[simp] theorem twoBranchRealPartCharge_one
    {d J : Type*} (charge : J → d → Int) (term : J) :
    twoBranchRealPartCharge charge (term, 1) = -charge term := by
  simp [twoBranchRealPartCharge]

/-- Exact character-family form of a scaled real part.  This is where both
the factor `1 / 2` and the conjugate/negative-charge branch are accounted for.
-/
theorem coe_scaled_re_finitePhaseCorrection_eq_twoBranch
    {d J : Type*} [Fintype d] [Fintype J]
    (scale : Real) (coefficient : J → Complex) (charge : J → d → Int)
    (phase : UnitAddTorus d) :
    ((scale * (finitePhaseCorrection coefficient charge phase).re : Real) :
        Complex) =
      finitePhaseCorrection
        (twoBranchRealPartCoefficient scale coefficient)
        (twoBranchRealPartCharge charge) phase := by
  unfold finitePhaseCorrection twoBranchRealPartCoefficient
    twoBranchRealPartCharge
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
  push_cast
  rw [Complex.re_eq_add_conj, map_sum]
  simp only [map_mul, ← mFourier_neg]
  rw [Finset.sum_add_distrib]
  ring_nf
  congr 1 <;> rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  all_goals
    apply Finset.sum_congr rfl
    intro term hterm
    ring

/-- A deterministic interaction-picture rotation distributes over a finite
phase-character family and only changes its deterministic coefficients. -/
theorem phaseRenormalize_finitePhaseCorrection
    {d J : Type*} [Fintype d] [Fintype J]
    (theta : Real) (coefficient : J → Complex) (charge : J → d → Int)
    (phase : UnitAddTorus d) :
    phaseRenormalize theta
        (finitePhaseCorrection coefficient charge phase) =
      finitePhaseCorrection
        (fun term ↦ phaseFactor theta * coefficient term) charge phase := by
  unfold phaseRenormalize finitePhaseCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro term hterm
  ring

/-! ## The Physlib quadratic `J1` family -/

/-- Thin adapter from the physical unit-coupling first Picard coefficient to
the already proved finite oscillatory Haar sum on `QuadraticPhaseTerm`. -/
theorem physlibQuadraticFirstPicardCoefficient_eq_finiteHaarOscillatorySum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (time : Real) (observed : Lattice.Site N) :
    physlibQuadraticFirstPicardCoefficient
        m kappa radius phase time observed =
      finiteHaarOscillatorySum
        (freeQuadraticDuhamelCoefficient
          (physlibQuadraticCoupling m kappa 1 observed)
          m observed radius)
        quadraticPhaseCharge
        (quadraticPhaseMismatch (modeFrequency m) observed)
        time phase := by
  unfold physlibQuadraticFirstPicardCoefficient
  exact
    freeQuadraticInteractionPictureCorrection_eq_finiteHaarOscillatorySum
      (physlibQuadraticCoupling m kappa 1 observed)
      m observed radius (modeFrequency m) time phase

/-- The same `J1` adapter with the outer oscillatory wrapper unfolded to the
literal `finitePhaseCorrection` family. -/
theorem physlibQuadraticFirstPicardCoefficient_eq_finitePhaseCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (time : Real) (observed : Lattice.Site N) :
    physlibQuadraticFirstPicardCoefficient
        m kappa radius phase time observed =
      finitePhaseCorrection
        (oscillatoryCoefficient
          (freeQuadraticDuhamelCoefficient
            (physlibQuadraticCoupling m kappa 1 observed)
            m observed radius)
          (quadraticPhaseMismatch (modeFrequency m) observed) time)
        quadraticPhaseCharge phase := by
  simpa only [finiteHaarOscillatorySum] using
    physlibQuadraticFirstPicardCoefficient_eq_finiteHaarOscillatorySum
      m kappa radius phase time observed

/-! ## Positive/conjugate character family for the reconstructed coordinate -/

/-- One quadratic signed term together with the positive or conjugate branch
introduced by reconstructing a real modal coordinate. -/
abbrev QuadraticFirstPicardCoordinateCharacterTerm (N : Nat) :=
  QuadraticPhaseTerm N × Fin 2

/-- The deterministic coefficient of one quadratic Picard term after undoing
the observed interaction-picture phase. -/
def physlibQuadraticFirstPicardRotatedTermCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) : Complex :=
  phaseFactor (-(modeFrequency m observed * time)) *
    oscillatoryCoefficient
      (freeQuadraticDuhamelCoefficient
        (physlibQuadraticCoupling m kappa 1 observed)
        m observed radius)
      (quadraticPhaseMismatch (modeFrequency m) observed) time term

/-- Exact real-coordinate scale.  The division is exposed here only on the
strictly positive-frequency branch of the coefficient below. -/
def physlibQuadraticFirstPicardCoordinateScale
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N) : Real :=
  Real.sqrt (2 * modeFrequency m observed) / modeFrequency m observed

/-- Deterministic coefficient for the two-branch real-coordinate family.
At positive frequency it contains the exact scale `sqrt(2*omega)/omega` and
the real-part factor `1/2`.  At zero frequency it is set to zero, matching the
separate tensor-decoupling theorem used in the global identity. -/
def physlibQuadraticFirstPicardCoordinateCharacterCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) : Complex :=
  if 0 < modeFrequency m observed then
    twoBranchRealPartCoefficient
      (physlibQuadraticFirstPicardCoordinateScale m observed)
      (physlibQuadraticFirstPicardRotatedTermCoefficient
        m kappa radius time observed) entry
  else 0

/-- Charge of a real-coordinate character: `q` on the positive branch and
`-q` on the conjugate branch. -/
def physlibQuadraticFirstPicardCoordinateCharacterCharge
    {N : Nat} [NeZero N]
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    Lattice.Site N → Int :=
  twoBranchRealPartCharge quadraticPhaseCharge entry

/-- The complete finite positive/conjugate phase-character family for the
real first-Picard modal coordinate. -/
def physlibQuadraticFirstPicardCoordinateCharacterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (phase : UnitAddTorus (Lattice.Site N)) : Complex :=
  finitePhaseCorrection
    (physlibQuadraticFirstPicardCoordinateCharacterCoefficient
      m kappa radius time observed)
    physlibQuadraticFirstPicardCoordinateCharacterCharge phase

@[simp] theorem physlibQuadraticFirstPicardCoordinateCharacterCharge_zero
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    physlibQuadraticFirstPicardCoordinateCharacterCharge (term, 0) =
      quadraticPhaseCharge term := by
  simp [physlibQuadraticFirstPicardCoordinateCharacterCharge]

@[simp] theorem physlibQuadraticFirstPicardCoordinateCharacterCharge_one
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    physlibQuadraticFirstPicardCoordinateCharacterCharge (term, 1) =
      -quadraticPhaseCharge term := by
  simp [physlibQuadraticFirstPicardCoordinateCharacterCharge]

@[simp] theorem physlibQuadraticFirstPicardCoordinateCharacterCoefficient_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    (hpositive : 0 < modeFrequency m observed) :
    physlibQuadraticFirstPicardCoordinateCharacterCoefficient
        m kappa radius time observed (term, 0) =
      (((physlibQuadraticFirstPicardCoordinateScale m observed / 2 : Real) :
          Complex) *
        physlibQuadraticFirstPicardRotatedTermCoefficient
          m kappa radius time observed term) := by
  simp [physlibQuadraticFirstPicardCoordinateCharacterCoefficient, hpositive]

@[simp] theorem physlibQuadraticFirstPicardCoordinateCharacterCoefficient_one
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    (hpositive : 0 < modeFrequency m observed) :
    physlibQuadraticFirstPicardCoordinateCharacterCoefficient
        m kappa radius time observed (term, 1) =
      (((physlibQuadraticFirstPicardCoordinateScale m observed / 2 : Real) :
          Complex) *
        starRingEnd Complex
          (physlibQuadraticFirstPicardRotatedTermCoefficient
            m kappa radius time observed term)) := by
  simp [physlibQuadraticFirstPicardCoordinateCharacterCoefficient, hpositive]

/-- At positive observed frequency, applying coordinate reconstruction to
the exact `J1` family gives the complete two-branch character family. -/
theorem coe_interactionPictureCorrectionCoordinate_firstPicard_eq_characterFamily_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (time : Real) (observed : Lattice.Site N)
    (hpositive : 0 < modeFrequency m observed) :
    ((interactionPictureCorrectionCoordinate
        (modeFrequency m observed) time
        (physlibQuadraticFirstPicardCoefficient
          m kappa radius phase time observed) : Real) : Complex) =
      physlibQuadraticFirstPicardCoordinateCharacterFamily
        m kappa radius time observed phase := by
  rw [physlibQuadraticFirstPicardCoefficient_eq_finitePhaseCorrection]
  unfold interactionPictureCorrectionCoordinate
  rw [phaseRenormalize_finitePhaseCorrection]
  calc
    ((Real.sqrt (2 * modeFrequency m observed) *
          (finitePhaseCorrection
            (fun term ↦
              phaseFactor (-(modeFrequency m observed * time)) *
                oscillatoryCoefficient
                  (freeQuadraticDuhamelCoefficient
                    (physlibQuadraticCoupling m kappa 1 observed)
                    m observed radius)
                  (quadraticPhaseMismatch (modeFrequency m) observed)
                  time term)
            quadraticPhaseCharge phase).re /
          modeFrequency m observed : Real) : Complex) =
        (((physlibQuadraticFirstPicardCoordinateScale m observed *
          (finitePhaseCorrection
            (physlibQuadraticFirstPicardRotatedTermCoefficient
              m kappa radius time observed)
            quadraticPhaseCharge phase).re : Real) : Complex)) := by
      unfold physlibQuadraticFirstPicardCoordinateScale
        physlibQuadraticFirstPicardRotatedTermCoefficient
      congr 1
      ring
    _ = finitePhaseCorrection
          (twoBranchRealPartCoefficient
            (physlibQuadraticFirstPicardCoordinateScale m observed)
            (physlibQuadraticFirstPicardRotatedTermCoefficient
              m kappa radius time observed))
          (twoBranchRealPartCharge quadraticPhaseCharge) phase :=
      coe_scaled_re_finitePhaseCorrection_eq_twoBranch
        (physlibQuadraticFirstPicardCoordinateScale m observed)
        (physlibQuadraticFirstPicardRotatedTermCoefficient
          m kappa radius time observed)
        quadraticPhaseCharge phase
    _ = physlibQuadraticFirstPicardCoordinateCharacterFamily
          m kappa radius time observed phase := by
      unfold physlibQuadraticFirstPicardCoordinateCharacterFamily
        physlibQuadraticFirstPicardCoordinateCharacterCoefficient
        physlibQuadraticFirstPicardCoordinateCharacterCharge
      simp only [if_pos hpositive]

/-- The coordinate character family vanishes at a zero observed frequency.
This is the family-side endpoint paired below with the tensor-decoupled
vanishing theorem for the physical first Picard coefficient. -/
theorem physlibQuadraticFirstPicardCoordinateCharacterFamily_eq_zero_of_modeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (time : Real) (observed : Lattice.Site N)
    (hzero : modeFrequency m observed = 0) :
    physlibQuadraticFirstPicardCoordinateCharacterFamily
      m kappa radius time observed phase = 0 := by
  unfold physlibQuadraticFirstPicardCoordinateCharacterFamily
    physlibQuadraticFirstPicardCoordinateCharacterCoefficient
    finitePhaseCorrection
  simp [hzero]

/-- Global exact character-family identity for the real first-Picard modal
history.  The zero-frequency case is discharged by the tensor-decoupling
theorem for `A1`, not by cancelling the coordinate denominator. -/
theorem coe_physlibQuadraticFirstPicardModalHistory_eq_characterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N))
    (time : Real) (observed : Lattice.Site N) :
    ((physlibQuadraticFirstPicardModalHistory
        m kappa radius phase time observed : Real) : Complex) =
      physlibQuadraticFirstPicardCoordinateCharacterFamily
        m kappa radius time observed phase := by
  by_cases hpositive : 0 < modeFrequency m observed
  · rw [physlibQuadraticFirstPicardModalHistory_apply]
    exact
      coe_interactionPictureCorrectionCoordinate_firstPicard_eq_characterFamily_of_pos
        m kappa radius phase time observed hpositive
  · have hzero : modeFrequency m observed = 0 :=
      le_antisymm (le_of_not_gt hpositive) (modeFrequency_nonneg m observed)
    have hcoefficient :=
      physlibQuadraticFirstPicardCoefficient_eq_zero_of_modeFrequency_eq_zero
        m kappa radius phase time observed hzero
    rw [physlibQuadraticFirstPicardModalHistory_apply, hcoefficient, hzero,
      interactionPictureCorrectionCoordinate_zero,
      physlibQuadraticFirstPicardCoordinateCharacterFamily_eq_zero_of_modeFrequency_eq_zero
        m kappa radius phase time observed hzero]
    norm_num

end

end ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
