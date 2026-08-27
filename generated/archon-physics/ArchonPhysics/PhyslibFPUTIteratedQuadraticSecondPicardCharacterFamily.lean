import ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
import ArchonPhysics.NestedOscillatoryIntegral

/-!
# Character tree for the iterated quadratic second-Picard term

The quadratic part of the Physlib/FPUT second Picard source inserts the real
first-Picard history `Q1` into exactly one of the two ordered input slots of
the polarized quadratic tensor, while the other slot retains the free history
`Q0`.  This module records that finite tree explicitly.  Besides the two
outer slots, an index retains the sign of the free real coordinate and the
positive/conjugate branch of the inner first-Picard coordinate family.

The time coefficient is the exact triangular integral supplied by
`NestedOscillatoryIntegral`.  Zero-frequency modes are treated through the
existing tensor and first-Picard decoupling theorems; no frequency division is
cancelled at zero.  All results are finite-volume identities.
-/

namespace ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open scoped ComplexConjugate Interval

noncomputable section

/-! ## Generic finite-character and conjugation adapters -/

/-- Ordinary multiplication of two finite character families uses the
product index and adds their charges. -/
theorem finitePhaseCorrection_mul_eq_productCorrection
    {d J K : Type*} [Fintype d] [Fintype J] [Fintype K]
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int)
    (phase : UnitAddTorus d) :
    finitePhaseCorrection leftCoefficient leftCharge phase *
        finitePhaseCorrection rightCoefficient rightCharge phase =
      finitePhaseCorrection
        (fun pair : J × K ↦
          leftCoefficient pair.1 * rightCoefficient pair.2)
        (fun pair : J × K ↦
          leftCharge pair.1 + rightCharge pair.2) phase := by
  classical
  unfold finitePhaseCorrection
  rw [Finset.sum_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro leftTerm hleftTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rightTerm hrightTerm
  rw [mFourier_add]
  ring

/-- Complex conjugation reverses the mismatch of the canonical oscillatory
integral. -/
theorem star_oscillatoryIntegral (mismatch time : Real) :
    starRingEnd Complex (oscillatoryIntegral mismatch time) =
      oscillatoryIntegral (-mismatch) time := by
  unfold oscillatoryIntegral
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp
  rw [← Complex.exp_conj]
  congr 1
  simp

/-! ## Time-resolved branches of the real first-Picard coordinate -/

/-- Real sign attached to the original (`0`) or conjugate (`1`) coordinate
branch. -/
def firstPicardCoordinateBranchSign (branch : Fin 2) : Real :=
  if branch = 0 then 1 else -1

@[simp] theorem firstPicardCoordinateBranchSign_zero :
    firstPicardCoordinateBranchSign (0 : Fin 2) = 1 := by
  simp [firstPicardCoordinateBranchSign]

@[simp] theorem firstPicardCoordinateBranchSign_one :
    firstPicardCoordinateBranchSign (1 : Fin 2) = -1 := by
  simp [firstPicardCoordinateBranchSign]

/-- The inverse interaction-picture carrier is an exponential at frequency
`-omega`. -/
theorem phaseFactor_neg_frequency_mul_time (omega time : Real) :
    phaseFactor (-(omega * time)) =
      Complex.exp ((Complex.I * (-omega : Real)) * time) := by
  unfold phaseFactor
  congr 1
  push_cast
  ring

/-- Conjugating the inverse carrier reverses its frequency. -/
theorem star_phaseFactor_neg_frequency_mul_time (omega time : Real) :
    starRingEnd Complex (phaseFactor (-(omega * time))) =
      Complex.exp ((Complex.I * (omega : Real)) * time) := by
  rw [phaseFactor_neg_frequency_mul_time, ← Complex.exp_conj]
  congr 1
  simp

/-- Inner mismatch after choosing the original or conjugate real-coordinate
branch. -/
def firstPicardCoordinateBranchMismatch
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) : Real :=
  firstPicardCoordinateBranchSign entry.2 *
    quadraticPhaseMismatch (modeFrequency m) innerObserved entry.1

/-- Time-independent part of one first-Picard real-coordinate branch.  The
positive-frequency guard is the same one used by the established `Q1`
character family. -/
def firstPicardCoordinateBranchStaticCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) : Complex :=
  if 0 < modeFrequency m innerObserved then
    (((physlibQuadraticFirstPicardCoordinateScale m innerObserved / 2 : Real) :
        Complex) *
      if entry.2 = 0 then
        freeQuadraticDuhamelCoefficient
          (physlibQuadraticCoupling m kappa 1 innerObserved)
          m innerObserved radius entry.1
      else
        starRingEnd Complex
          (freeQuadraticDuhamelCoefficient
            (physlibQuadraticCoupling m kappa 1 innerObserved)
            m innerObserved radius entry.1))
  else 0

/-- Exact time-resolved normal form of one coordinate branch: a static
coefficient, one carrier phase, and an inner oscillatory integral whose
mismatch changes sign under conjugation. -/
theorem physlibQuadraticFirstPicardCoordinateCharacterCoefficient_eq_timeResolved
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    physlibQuadraticFirstPicardCoordinateCharacterCoefficient
        m kappa radius time innerObserved entry =
      firstPicardCoordinateBranchStaticCoefficient
          m kappa radius innerObserved entry *
        Complex.exp
          ((Complex.I *
            (-(firstPicardCoordinateBranchSign entry.2 *
              modeFrequency m innerObserved) : Real)) * time) *
        oscillatoryIntegral
          (firstPicardCoordinateBranchMismatch m innerObserved entry) time := by
  by_cases hpositive : 0 < modeFrequency m innerObserved
  · rcases entry with ⟨innerTerm, branch⟩
    by_cases hbranch : branch = 0
    · subst branch
      rw [physlibQuadraticFirstPicardCoordinateCharacterCoefficient_zero
        m kappa radius time innerObserved innerTerm hpositive]
      unfold firstPicardCoordinateBranchStaticCoefficient
        firstPicardCoordinateBranchMismatch
      rw [if_pos hpositive]
      simp only [firstPicardCoordinateBranchSign_zero, Fin.isValue, one_mul]
      simp only [if_true]
      unfold physlibQuadraticFirstPicardRotatedTermCoefficient
        oscillatoryCoefficient
      rw [phaseFactor_neg_frequency_mul_time]
      ring_nf
    · have hbranchOne : branch = 1 := Fin.eq_one_of_ne_zero branch hbranch
      subst branch
      rw [physlibQuadraticFirstPicardCoordinateCharacterCoefficient_one
        m kappa radius time innerObserved innerTerm hpositive]
      unfold firstPicardCoordinateBranchStaticCoefficient
        firstPicardCoordinateBranchMismatch
      rw [if_pos hpositive]
      simp only [firstPicardCoordinateBranchSign_one,
        Fin.isValue, one_ne_zero, if_false, neg_mul, neg_neg]
      unfold physlibQuadraticFirstPicardRotatedTermCoefficient
        oscillatoryCoefficient
      rw [map_mul, map_mul, star_phaseFactor_neg_frequency_mul_time,
        star_oscillatoryIntegral]
      ring_nf
  · unfold physlibQuadraticFirstPicardCoordinateCharacterCoefficient
      firstPicardCoordinateBranchStaticCoefficient
    simp only [if_neg hpositive, zero_mul]

/-! ## The finite iterated-quadratic tree -/

/-- The slot opposite a selected input slot of a quadratic tensor. -/
def otherQuadraticSlot (slot : Fin 2) : Fin 2 :=
  if slot = 0 then 1 else 0

@[simp] theorem otherQuadraticSlot_zero :
    otherQuadraticSlot (0 : Fin 2) = 1 := by
  simp [otherQuadraticSlot]

@[simp] theorem otherQuadraticSlot_one :
    otherQuadraticSlot (1 : Fin 2) = 0 := by
  simp [otherQuadraticSlot]

/-- A complete iterated-quadratic character tree records the two outer input
modes, the slot occupied by `Q1`, the sign of the opposite free `Q0` leg, and
one term of the positive/conjugate `Q1` family. -/
abbrev IteratedQuadraticSecondPicardCharacterTerm (N : Nat) :=
  (Fin 2 → Lattice.Site N) ×
    (Fin 2 × (Fin 2 × QuadraticFirstPicardCoordinateCharacterTerm N))

/-- Outer input modes of a character tree. -/
def iteratedQuadraticOuterModes {N : Nat}
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Fin 2 → Lattice.Site N :=
  term.1

/-- The outer slot occupied by `Q1`. -/
def iteratedQuadraticFirstPicardSlot {N : Nat}
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Fin 2 :=
  term.2.1

/-- Sign branch of the free `Q0` leg. -/
def iteratedQuadraticFreeSign {N : Nat}
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Fin 2 :=
  term.2.2.1

/-- Inner quadratic term and its positive/conjugate coordinate branch. -/
def iteratedQuadraticInnerEntry {N : Nat}
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    QuadraticFirstPicardCoordinateCharacterTerm N :=
  term.2.2.2

/-- Outer mode on which the first-Picard history is evaluated. -/
def iteratedQuadraticFirstPicardMode {N : Nat}
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Lattice.Site N :=
  iteratedQuadraticOuterModes term (iteratedQuadraticFirstPicardSlot term)

/-- Outer mode carried by the remaining free coordinate. -/
def iteratedQuadraticFreeMode {N : Nat}
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Lattice.Site N :=
  iteratedQuadraticOuterModes term
    (otherQuadraticSlot (iteratedQuadraticFirstPicardSlot term))

/-- Charge of the signed free outer leg. -/
def iteratedQuadraticFreeCharge {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Lattice.Site N → Int :=
  (binarySignedMode (iteratedQuadraticFreeMode term)
    (iteratedQuadraticFreeSign term)).charge

/-- Total initial-phase charge: free-leg charge plus the charge of the
selected positive/conjugate `Q1` branch. -/
def iteratedQuadraticSecondPicardCharge {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Lattice.Site N → Int :=
  iteratedQuadraticFreeCharge term +
    physlibQuadraticFirstPicardCoordinateCharacterCharge
      (iteratedQuadraticInnerEntry term)

/-- Time-dependent coefficient of one signed free coordinate, with its
initial character removed. -/
def freeCoordinateCharacterTimeCoefficient
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (mode : Lattice.Site N) (sign : Fin 2) : Complex :=
  ((radius mode / 2 : Real) : Complex) *
    Complex.exp
      ((Complex.I *
        (-(chargeFrequency (binarySignedMode mode sign).charge frequency) :
          Real)) * time)

/-- One free real modal coordinate is a two-term initial-character family
with its free carrier isolated in the deterministic coefficient. -/
theorem coe_freeRealModeCoordinate_eq_timeCharacterFamily
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) (mode : Lattice.Site N) :
    (freeRealModeCoordinate radius frequency time phase mode : Complex) =
      finitePhaseCorrection
        (freeCoordinateCharacterTimeCoefficient radius frequency time mode)
        (fun sign : Fin 2 ↦ (binarySignedMode mode sign).charge) phase := by
  rw [coe_freeRealModeCoordinate_eq_binarySignedSum]
  unfold finitePhaseCorrection freeCoordinateCharacterTimeCoefficient
  apply Finset.sum_congr rfl
  intro sign hsign
  unfold binarySignedCharacter
  rw [SignedMode.phaseFactor_eq_mFourier,
    mFourier_physicalFreePhaseEvolution]
  ring

/-- Time-dependent coefficient for fixed outer modes, one selected `Q1`
slot, and the pair consisting of a free sign and an inner `Q1` entry. -/
def iteratedQuadraticSlotTimeCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (modes : Fin 2 → Lattice.Site N) (firstPicardSlot : Fin 2)
    (pair : Fin 2 × QuadraticFirstPicardCoordinateCharacterTerm N) : Complex :=
  (interactionTensor m 3
      (Fin.cons observed modes) : Complex) *
    freeCoordinateCharacterTimeCoefficient radius (modeFrequency m) time
      (modes (otherQuadraticSlot firstPicardSlot)) pair.1 *
    physlibQuadraticFirstPicardCoordinateCharacterCoefficient
      m kappa radius time (modes firstPicardSlot) pair.2

/-- Charge for a fixed outer placement and its free-sign/inner-entry pair. -/
def iteratedQuadraticSlotCharge
    {N : Nat} [NeZero N]
    (modes : Fin 2 → Lattice.Site N) (firstPicardSlot : Fin 2)
    (pair : Fin 2 × QuadraticFirstPicardCoordinateCharacterTerm N) :
    Lattice.Site N → Int :=
  (binarySignedMode (modes (otherQuadraticSlot firstPicardSlot)) pair.1).charge +
    physlibQuadraticFirstPicardCoordinateCharacterCharge pair.2

/-- Time-dependent coefficient of the complexified polarized cross
contraction before the outer forced-mode factor is inserted. -/
def iteratedQuadraticCrossTimeCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Complex :=
  iteratedQuadraticSlotTimeCoefficient m kappa radius time observed term.1
    term.2.1 term.2.2

/-- For fixed outer modes and placement, the tensor multiple of the free
coordinate times `Q1` is the product-index character family. -/
theorem interactionTensor_mul_free_mul_firstPicard_eq_slotCharacterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N)
    (modes : Fin 2 → Lattice.Site N) (firstPicardSlot : Fin 2) :
    (interactionTensor m 3 (Fin.cons observed modes) : Complex) *
        (freeRealModeCoordinate radius (modeFrequency m) time phase
          (modes (otherQuadraticSlot firstPicardSlot)) : Complex) *
        (physlibQuadraticFirstPicardModalHistory
          m kappa radius phase time (modes firstPicardSlot) : Real) =
      finitePhaseCorrection
        (iteratedQuadraticSlotTimeCoefficient
          m kappa radius time observed modes firstPicardSlot)
        (iteratedQuadraticSlotCharge modes firstPicardSlot) phase := by
  classical
  rw [coe_freeRealModeCoordinate_eq_timeCharacterFamily]
  rw [show
    ((physlibQuadraticFirstPicardModalHistory
        m kappa radius phase time (modes firstPicardSlot) : Real) : Complex) =
      finitePhaseCorrection
        (physlibQuadraticFirstPicardCoordinateCharacterCoefficient
          m kappa radius time (modes firstPicardSlot))
        physlibQuadraticFirstPicardCoordinateCharacterCharge phase by
      simpa [physlibQuadraticFirstPicardCoordinateCharacterFamily] using
        coe_physlibQuadraticFirstPicardModalHistory_eq_characterFamily
          m kappa radius phase time (modes firstPicardSlot)]
  rw [show
    (interactionTensor m 3 (Fin.cons observed modes) : Complex) *
        finitePhaseCorrection
          (freeCoordinateCharacterTimeCoefficient radius (modeFrequency m)
            time (modes (otherQuadraticSlot firstPicardSlot)))
          (fun sign : Fin 2 ↦
            (binarySignedMode
              (modes (otherQuadraticSlot firstPicardSlot)) sign).charge) phase *
        finitePhaseCorrection
          (physlibQuadraticFirstPicardCoordinateCharacterCoefficient
            m kappa radius time (modes firstPicardSlot))
          physlibQuadraticFirstPicardCoordinateCharacterCharge phase =
      (interactionTensor m 3 (Fin.cons observed modes) : Complex) *
        (finitePhaseCorrection
          (freeCoordinateCharacterTimeCoefficient radius (modeFrequency m)
            time (modes (otherQuadraticSlot firstPicardSlot)))
          (fun sign : Fin 2 ↦
            (binarySignedMode
              (modes (otherQuadraticSlot firstPicardSlot)) sign).charge) phase *
        finitePhaseCorrection
          (physlibQuadraticFirstPicardCoordinateCharacterCoefficient
            m kappa radius time (modes firstPicardSlot))
          physlibQuadraticFirstPicardCoordinateCharacterCharge phase) by ring]
  rw [finitePhaseCorrection_mul_eq_productCorrection]
  unfold finitePhaseCorrection iteratedQuadraticSlotTimeCoefficient
    iteratedQuadraticSlotCharge
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair hpair
  ring

/-- Flattening the explicit `(outer modes, Q1 slot, free sign, inner entry)`
tree is exactly a sum over fixed outer modes and slots. -/
theorem iteratedQuadraticCrossCharacterFamily_eq_sum_slots
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    finitePhaseCorrection
        (iteratedQuadraticCrossTimeCoefficient
          m kappa radius time observed)
        iteratedQuadraticSecondPicardCharge phase =
      ∑ modes : Fin 2 → Lattice.Site N, ∑ firstPicardSlot : Fin 2,
        finitePhaseCorrection
          (iteratedQuadraticSlotTimeCoefficient
            m kappa radius time observed modes firstPicardSlot)
          (iteratedQuadraticSlotCharge modes firstPicardSlot) phase := by
  classical
  unfold finitePhaseCorrection
  calc
    (∑ term : IteratedQuadraticSecondPicardCharacterTerm N,
        iteratedQuadraticCrossTimeCoefficient
            m kappa radius time observed term *
          mFourier (iteratedQuadraticSecondPicardCharge term) phase) =
        ∑ modes : Fin 2 → Lattice.Site N,
          ∑ rest : Fin 2 ×
              (Fin 2 × QuadraticFirstPicardCoordinateCharacterTerm N),
            iteratedQuadraticCrossTimeCoefficient
                m kappa radius time observed (modes, rest) *
              mFourier
                (iteratedQuadraticSecondPicardCharge (modes, rest)) phase :=
      Fintype.sum_prod_type _
    _ = ∑ modes : Fin 2 → Lattice.Site N, ∑ firstPicardSlot : Fin 2,
        ∑ pair : Fin 2 × QuadraticFirstPicardCoordinateCharacterTerm N,
          iteratedQuadraticCrossTimeCoefficient m kappa radius time observed
              (modes, firstPicardSlot, pair) *
            mFourier
              (iteratedQuadraticSecondPicardCharge
                (modes, firstPicardSlot, pair)) phase := by
      apply Finset.sum_congr rfl
      intro modes hmodes
      exact Fintype.sum_prod_type _
    _ = ∑ modes : Fin 2 → Lattice.Site N, ∑ firstPicardSlot : Fin 2,
        ∑ pair : Fin 2 × QuadraticFirstPicardCoordinateCharacterTerm N,
          iteratedQuadraticSlotTimeCoefficient
              m kappa radius time observed modes firstPicardSlot pair *
            mFourier
              (iteratedQuadraticSlotCharge modes firstPicardSlot pair) phase := by
      rfl

/-- Exact finite-character expansion of the complexified polarized outer
cross contraction, preserving both ordered `Q1` placements. -/
theorem coe_quadraticTensorCrossContraction_free_firstPicard_eq_characterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    ((quadraticTensorCrossContraction m observed
        (freeWeightedConfiguration radius (modeFrequency m) time phase)
        (physlibQuadraticFirstPicardModalHistory
          m kappa radius phase time) : Real) : Complex) =
      finitePhaseCorrection
        (iteratedQuadraticCrossTimeCoefficient
          m kappa radius time observed)
        iteratedQuadraticSecondPicardCharge phase := by
  classical
  unfold quadraticTensorCrossContraction
  push_cast
  simp_rw [freeWeightedConfiguration_apply]
  calc
    (∑ modes : Fin 2 → Lattice.Site N,
      (interactionTensor m 3 (Fin.cons observed modes) : Complex) *
        (((freeRealModeCoordinate radius (modeFrequency m) time phase (modes 0) :
              Real) : Complex) *
            ((physlibQuadraticFirstPicardModalHistory
              m kappa radius phase time (modes 1) : Real) : Complex) +
          ((physlibQuadraticFirstPicardModalHistory
              m kappa radius phase time (modes 0) : Real) : Complex) *
            (freeRealModeCoordinate radius (modeFrequency m) time phase (modes 1) :
              Complex))) =
        ∑ modes : Fin 2 → Lattice.Site N,
          (∑ firstPicardSlot : Fin 2,
            finitePhaseCorrection
              (iteratedQuadraticSlotTimeCoefficient
                m kappa radius time observed modes firstPicardSlot)
              (iteratedQuadraticSlotCharge modes firstPicardSlot) phase) := by
      apply Finset.sum_congr rfl
      intro modes hmodes
      rw [Fin.sum_univ_two]
      rw [← interactionTensor_mul_free_mul_firstPicard_eq_slotCharacterFamily
          m kappa radius phase time observed modes 0,
        ← interactionTensor_mul_free_mul_firstPicard_eq_slotCharacterFamily
          m kappa radius phase time observed modes 1]
      simp only [otherQuadraticSlot_zero, otherQuadraticSlot_one]
      ring
    _ = finitePhaseCorrection
        (iteratedQuadraticCrossTimeCoefficient
          m kappa radius time observed)
        iteratedQuadraticSecondPicardCharge phase :=
      (iteratedQuadraticCrossCharacterFamily_eq_sum_slots
        m kappa radius phase time observed).symm

/-! ## Output rotation and the nested second-Picard coefficient -/

/-- Unit outer quadratic forcing coefficient in the positive-frequency
complex-mode equation. -/
def physlibIteratedQuadraticOuterCoupling
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (observed : Lattice.Site N) : Complex :=
  forcedModeSource (modeFrequency m observed) (-kappa)

/-- Mismatch of the inner first-Picard oscillatory integral after selecting
the original or conjugate coordinate branch. -/
def iteratedQuadraticInnerMismatch
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Real :=
  firstPicardCoordinateBranchMismatch m
    (iteratedQuadraticFirstPicardMode term)
    (iteratedQuadraticInnerEntry term)

/-- Outer mismatch before the inner first-Picard time integral.  It contains
the output frequency, the signed free-leg frequency, and the carrier
frequency of the chosen `Q1` coordinate branch. -/
def iteratedQuadraticOuterMismatch
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Real :=
  modeFrequency m observed -
    chargeFrequency (iteratedQuadraticFreeCharge term) (modeFrequency m) -
    firstPicardCoordinateBranchSign
        (iteratedQuadraticInnerEntry term).2 *
      modeFrequency m (iteratedQuadraticFirstPicardMode term)

/-- Time-independent coefficient of one complete iterated-quadratic tree.
The outer positive-frequency guard is explicit; the inner static coefficient
has its own established positive-frequency guard. -/
def iteratedQuadraticSecondPicardStaticCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Complex :=
  if 0 < modeFrequency m observed then
    physlibIteratedQuadraticOuterCoupling m kappa observed *
      (interactionTensor m 3
        (Fin.cons observed (iteratedQuadraticOuterModes term)) : Complex) *
      ((radius (iteratedQuadraticFreeMode term) / 2 : Real) : Complex) *
      firstPicardCoordinateBranchStaticCoefficient
        m kappa radius (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term)
  else 0

/-- Pointwise coefficient before replacing the two time layers by their
nested-integral coefficient. -/
def iteratedQuadraticSecondPicardRotatedTimeCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Complex :=
  if 0 < modeFrequency m observed then
    physlibIteratedQuadraticOuterCoupling m kappa observed *
      phaseFactor (modeFrequency m observed * time) *
      iteratedQuadraticCrossTimeCoefficient
        m kappa radius time observed term
  else 0

/-- The three carrier phases combine into the declared outer mismatch. -/
theorem output_free_firstPicard_carriers_eq_outerMismatch
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) (time : Real) :
    phaseFactor (modeFrequency m observed * time) *
        Complex.exp
          ((Complex.I *
            (-(chargeFrequency (iteratedQuadraticFreeCharge term)
              (modeFrequency m)) : Real)) * time) *
        Complex.exp
          ((Complex.I *
            (-(firstPicardCoordinateBranchSign
                (iteratedQuadraticInnerEntry term).2 *
              modeFrequency m (iteratedQuadraticFirstPicardMode term)) :
              Real)) * time) =
      Complex.exp
        ((Complex.I *
          (iteratedQuadraticOuterMismatch m observed term : Real)) * time) := by
  unfold phaseFactor iteratedQuadraticOuterMismatch
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Termwise time normal form: every complete tree is a static coefficient
times one outer exponential and one inner oscillatory integral. -/
theorem iteratedQuadraticSecondPicardRotatedTimeCoefficient_eq_timeResolved
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticSecondPicardRotatedTimeCoefficient
        m kappa radius time observed term =
      iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term *
        Complex.exp
          ((Complex.I *
            (iteratedQuadraticOuterMismatch m observed term : Real)) * time) *
        oscillatoryIntegral (iteratedQuadraticInnerMismatch m term) time := by
  by_cases hpositive : 0 < modeFrequency m observed
  · unfold iteratedQuadraticSecondPicardRotatedTimeCoefficient
      iteratedQuadraticSecondPicardStaticCoefficient
    rw [if_pos hpositive, if_pos hpositive]
    unfold iteratedQuadraticCrossTimeCoefficient
      iteratedQuadraticSlotTimeCoefficient
      freeCoordinateCharacterTimeCoefficient
      iteratedQuadraticInnerMismatch
    rw [physlibQuadraticFirstPicardCoordinateCharacterCoefficient_eq_timeResolved]
    calc
      _ = (physlibIteratedQuadraticOuterCoupling m kappa observed *
              (interactionTensor m 3
                (Fin.cons observed (iteratedQuadraticOuterModes term)) : Complex) *
              (((radius (iteratedQuadraticFreeMode term) / 2 : Real) : Complex) *
              firstPicardCoordinateBranchStaticCoefficient
                m kappa radius (iteratedQuadraticFirstPicardMode term)
                (iteratedQuadraticInnerEntry term)) *
            (phaseFactor (modeFrequency m observed * time) *
              Complex.exp
                ((Complex.I *
                  (-(chargeFrequency (iteratedQuadraticFreeCharge term)
                    (modeFrequency m)) : Real)) * time) *
              Complex.exp
                ((Complex.I *
                  (-(firstPicardCoordinateBranchSign
                      (iteratedQuadraticInnerEntry term).2 *
                    modeFrequency m (iteratedQuadraticFirstPicardMode term)) :
                    Real)) * time))) *
          oscillatoryIntegral (iteratedQuadraticInnerMismatch m term) time := by
            simp only [iteratedQuadraticOuterModes,
              iteratedQuadraticFirstPicardSlot, iteratedQuadraticFreeSign,
              iteratedQuadraticInnerEntry, iteratedQuadraticFirstPicardMode,
              iteratedQuadraticFreeMode, iteratedQuadraticFreeCharge,
              iteratedQuadraticInnerMismatch]
            ring_nf
      _ = _ := by
        rw [output_free_firstPicard_carriers_eq_outerMismatch]
        simp only [iteratedQuadraticInnerMismatch]
        ring
  · unfold iteratedQuadraticSecondPicardRotatedTimeCoefficient
      iteratedQuadraticSecondPicardStaticCoefficient
    simp [if_neg hpositive]

/-- An inner zero-frequency leg kills the static coefficient through the
physical interaction tensor, independently of the coordinate division. -/
theorem iteratedQuadraticSecondPicardStaticCoefficient_eq_zero_of_innerFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hzero : modeFrequency m (iteratedQuadraticFirstPicardMode term) = 0) :
    iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term = 0 := by
  have htensor := interactionTensor_cons_eq_zero_of_inputFrequency_eq_zero
    m observed (iteratedQuadraticOuterModes term)
      (iteratedQuadraticFirstPicardSlot term)
      (by simpa [iteratedQuadraticFirstPicardMode] using hzero)
  unfold iteratedQuadraticSecondPicardStaticCoefficient
  split_ifs
  · rw [htensor]
    simp
  · rfl

/-- The physical forced source is linear in the real cross contraction with
the displayed unit coefficient. -/
theorem forcedModeSource_neg_kappa_mul_eq_outerCoupling_mul
    (omega kappa cross : Real) :
    forcedModeSource omega (-(kappa * cross)) =
      forcedModeSource omega (-kappa) * (cross : Complex) := by
  unfold forcedModeSource
  push_cast
  ring

/-- Exact pointwise finite-character expansion of the P3 iterated-quadratic
source.  At zero observed frequency the physical tensor-decoupling theorem is
used directly. -/
theorem physlibQuadraticSecondPicardRotatedSource_eq_characterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    physlibQuadraticSecondPicardRotatedSource
        m kappa observed radius phase time =
      finitePhaseCorrection
        (iteratedQuadraticSecondPicardRotatedTimeCoefficient
          m kappa radius time observed)
        iteratedQuadraticSecondPicardCharge phase := by
  classical
  by_cases hpositive : 0 < modeFrequency m observed
  · unfold physlibQuadraticSecondPicardRotatedSource
    rw [forcedModeSource_neg_kappa_mul_eq_outerCoupling_mul]
    rw [coe_quadraticTensorCrossContraction_free_firstPicard_eq_characterFamily]
    unfold iteratedQuadraticSecondPicardRotatedTimeCoefficient
    unfold physlibIteratedQuadraticOuterCoupling finitePhaseCorrection
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro term hterm
    simp only [if_pos hpositive]
    ring
  · have hzero : modeFrequency m observed = 0 :=
      le_antisymm (le_of_not_gt hpositive) (modeFrequency_nonneg m observed)
    rw [physlibQuadraticSecondPicardRotatedSource_eq_zero_of_modeFrequency_eq_zero
      m kappa observed radius phase time hzero]
    unfold finitePhaseCorrection
      iteratedQuadraticSecondPicardRotatedTimeCoefficient
    symm
    apply Finset.sum_eq_zero
    intro term hterm
    rw [if_neg hpositive, zero_mul]

/-- Pointwise mismatch-sum form of the same P3 source. -/
theorem physlibQuadraticSecondPicardRotatedSource_eq_mismatchSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    physlibQuadraticSecondPicardRotatedSource
        m kappa observed radius phase time =
      ∑ term : IteratedQuadraticSecondPicardCharacterTerm N,
        (iteratedQuadraticSecondPicardStaticCoefficient
            m kappa radius observed term *
          mFourier (iteratedQuadraticSecondPicardCharge term) phase) *
          (Complex.exp
            ((Complex.I *
              (iteratedQuadraticOuterMismatch m observed term : Real)) * time) *
            oscillatoryIntegral
              (iteratedQuadraticInnerMismatch m term) time) := by
  rw [physlibQuadraticSecondPicardRotatedSource_eq_characterFamily]
  unfold finitePhaseCorrection
  apply Finset.sum_congr rfl
  intro term hterm
  rw [iteratedQuadraticSecondPicardRotatedTimeCoefficient_eq_timeResolved]
  ring

/-- Nested time coefficient of one complete iterated-quadratic tree. -/
def iteratedQuadraticSecondPicardNestedCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Complex :=
  iteratedQuadraticSecondPicardStaticCoefficient
      m kappa radius observed term *
    nestedOscillatoryIntegral
      (iteratedQuadraticOuterMismatch m observed term)
      (iteratedQuadraticInnerMismatch m term) time

/-- The integrated iterated-quadratic component of the P3 `A2` coefficient. -/
def physlibIteratedQuadraticSecondPicardCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) : Complex :=
  ∫ s in (0 : Real)..time,
    physlibQuadraticSecondPicardRotatedSource
      m kappa observed radius phase s

/-- Exact integrated character tree for the iterated-quadratic P3 `A2`
component. -/
theorem physlibIteratedQuadraticSecondPicardCoefficient_eq_characterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    physlibIteratedQuadraticSecondPicardCoefficient
        m kappa radius phase time observed =
      finitePhaseCorrection
        (iteratedQuadraticSecondPicardNestedCoefficient
          m kappa radius observed time)
        iteratedQuadraticSecondPicardCharge phase := by
  classical
  unfold physlibIteratedQuadraticSecondPicardCoefficient
  calc
    (∫ s in (0 : Real)..time,
      physlibQuadraticSecondPicardRotatedSource
        m kappa observed radius phase s) =
        ∫ s in (0 : Real)..time,
          ∑ term : IteratedQuadraticSecondPicardCharacterTerm N,
            (iteratedQuadraticSecondPicardStaticCoefficient
                m kappa radius observed term *
              mFourier (iteratedQuadraticSecondPicardCharge term) phase) *
              (Complex.exp
                ((Complex.I *
                  (iteratedQuadraticOuterMismatch m observed term : Real)) * s) *
                oscillatoryIntegral
                  (iteratedQuadraticInnerMismatch m term) s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact physlibQuadraticSecondPicardRotatedSource_eq_mismatchSum
        m kappa radius phase s observed
    _ = ∑ term : IteratedQuadraticSecondPicardCharacterTerm N,
        ∫ s in (0 : Real)..time,
          (iteratedQuadraticSecondPicardStaticCoefficient
              m kappa radius observed term *
            mFourier (iteratedQuadraticSecondPicardCharge term) phase) *
            (Complex.exp
              ((Complex.I *
                (iteratedQuadraticOuterMismatch m observed term : Real)) * s) *
              oscillatoryIntegral
                (iteratedQuadraticInnerMismatch m term) s) := by
      apply intervalIntegral.integral_finsetSum (μ := volume)
      intro term hterm
      exact
        (continuous_nestedOscillatoryIntegrand
          (iteratedQuadraticOuterMismatch m observed term)
          (iteratedQuadraticInnerMismatch m term)).const_mul
            (iteratedQuadraticSecondPicardStaticCoefficient
                m kappa radius observed term *
              mFourier (iteratedQuadraticSecondPicardCharge term) phase)
          |>.intervalIntegrable (μ := volume) 0 time
    _ = finitePhaseCorrection
        (iteratedQuadraticSecondPicardNestedCoefficient
          m kappa radius observed time)
        iteratedQuadraticSecondPicardCharge phase := by
      unfold finitePhaseCorrection
        iteratedQuadraticSecondPicardNestedCoefficient
        nestedOscillatoryIntegral
      apply Finset.sum_congr rfl
      intro term hterm
      rw [intervalIntegral.integral_const_mul]
      ring

/-- The complete iterated-quadratic character family vanishes at a
zero-frequency observed mode by the P3 physical decoupling theorem. -/
theorem physlibIteratedQuadraticSecondPicardCoefficient_eq_zero_of_modeFrequency_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N)
    (hzero : modeFrequency m observed = 0) :
    physlibIteratedQuadraticSecondPicardCoefficient
        m kappa radius phase time observed = 0 := by
  unfold physlibIteratedQuadraticSecondPicardCoefficient
  have hsource :
      physlibQuadraticSecondPicardRotatedSource
          m kappa observed radius phase = 0 := by
    funext s
    exact physlibQuadraticSecondPicardRotatedSource_eq_zero_of_modeFrequency_eq_zero
      m kappa observed radius phase s hzero
  rw [hsource]
  simp

end

end ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
