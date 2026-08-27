import ArchonPhysics.FreeFPUTCrossOrbitRealDecay
import ArchonPhysics.CubicVertexInfraredBound
import ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
import ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder

/-!
# Explicit volume dependence of the free FPUT cross-orbit coefficient

The cross-swap-orbit coherent remainder is supported on the exceptional
zero-charge fiber.  This file makes the finite-volume size of that fiber
explicit: a zero-charge quadratic term consists of one repeated input mode
with the two opposite binary phase signs, so there are exactly `2 * N` such
terms on a periodic chain of length `N`.

Consequently, a uniform bound `coefficientBound` on each free quadratic
Duhamel coefficient gives an explicit `(2 * N)^2 * coefficientBound^2`
bound on the zero-charge cross coefficient.  Combined with the existing
inverse-time estimate, this records precisely what is and is not uniform in
volume.  In particular, no volume-uniform coefficient bound is inferred from
positivity of the masses alone.
-/

namespace ArchonPhysics.FreeFPUTCrossOrbitCoefficientVolumeBound

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTCrossOrbitRealDecay
open ArchonPhysics.FreeFPUTCrossOrbitZeroChargeBridge
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTNonzeroChargeFiberClassification
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder
open ArchonPhysics.CubicVertexInfraredBound
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling

noncomputable section

/-- The finite set of quadratic phase terms in the exceptional zero-charge
fiber. -/
def zeroChargeQuadraticPhaseTerms (N : Nat) [NeZero N] :
    Finset (QuadraticPhaseTerm N) := by
  classical
  exact Finset.univ.filter fun term => quadraticPhaseCharge term = 0

/-- The other element of the two-point binary phase index. -/
def oppositeBinaryPhaseIndex (sign : Fin 2) : Fin 2 :=
  if sign = 0 then 1 else 0

theorem oppositeBinaryPhaseIndex_ne (sign : Fin 2) :
    sign ≠ oppositeBinaryPhaseIndex sign := by
  fin_cases sign <;> simp [oppositeBinaryPhaseIndex]

/-- The zero-charge term with a prescribed repeated mode and first sign. -/
def zeroChargeQuadraticPhaseTerm
    {N : Nat} [NeZero N] (mode : Lattice.Site N) (sign : Fin 2) :
    QuadraticPhaseTerm N :=
  (fun _ => mode, (sign, oppositeBinaryPhaseIndex sign))

@[simp] theorem quadraticPhaseCharge_zeroChargeQuadraticPhaseTerm
    {N : Nat} [NeZero N] (mode : Lattice.Site N) (sign : Fin 2) :
    quadraticPhaseCharge (zeroChargeQuadraticPhaseTerm mode sign) = 0 := by
  apply quadraticPhaseCharge_eq_zero_of_sameMode_oppositeSigns
  · rfl
  · exact oppositeBinaryPhaseIndex_ne sign

/-- Zero quadratic charge is equivalent to a repeated input mode carrying
opposite binary phase signs. -/
theorem quadraticPhaseCharge_eq_zero_iff_repeated_opposite
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N) :
    quadraticPhaseCharge term = 0 ↔
      term.1 0 = term.1 1 ∧ term.2.1 ≠ term.2.2 := by
  constructor
  · intro hcharge
    have hatMode := congrFun hcharge (term.1 0)
    have hmodes : term.1 0 = term.1 1 := by
      by_contra hne
      rcases term with ⟨modes, signs⟩
      rcases signs with ⟨leftSign, rightSign⟩
      fin_cases leftSign <;> fin_cases rightSign <;>
        simp [quadraticPhaseCharge, binarySignedMode, SignedMode.charge,
          binaryPhaseSign, hne] at hatMode
    refine ⟨hmodes, ?_⟩
    by_contra hsigns
    have hsignsEq : term.2.1 = term.2.2 := hsigns
    rcases term with ⟨modes, signs⟩
    rcases signs with ⟨leftSign, rightSign⟩
    fin_cases leftSign <;> fin_cases rightSign <;>
      simp_all [quadraticPhaseCharge, binarySignedMode, SignedMode.charge,
        binaryPhaseSign]
  · rintro ⟨hmodes, hsigns⟩
    exact quadraticPhaseCharge_eq_zero_of_sameMode_oppositeSigns
      term hmodes hsigns

/-- A zero-charge term is determined by its repeated mode and its first
binary phase sign. -/
theorem zeroCharge_term_eq_of_mode_zero_sign_zero_eq
    {N : Nat} [NeZero N] {left right : QuadraticPhaseTerm N}
    (hleft : quadraticPhaseCharge left = 0)
    (hright : quadraticPhaseCharge right = 0)
    (hmode : left.1 0 = right.1 0)
    (hsign : left.2.1 = right.2.1) :
    left = right := by
  have hleftStructure :=
    (quadraticPhaseCharge_eq_zero_iff_repeated_opposite left).1 hleft
  have hrightStructure :=
    (quadraticPhaseCharge_eq_zero_iff_repeated_opposite right).1 hright
  apply Prod.ext
  · funext r
    fin_cases r
    · exact hmode
    · exact hleftStructure.1.symm.trans (hmode.trans hrightStructure.1)
  · apply Prod.ext
    · exact hsign
    · apply Fin.ext
      have hfirstVal := congrArg Fin.val hsign
      have hleftFirst := left.2.1.isLt
      have hleftSecond := left.2.2.isLt
      have hrightFirst := right.2.1.isLt
      have hrightSecond := right.2.2.isLt
      omega

/-- The exceptional zero-charge fiber has at most `2 * N` elements.  The
reverse inequality also holds, but this upper bound is the exact input needed
for the coefficient estimate below. -/
theorem card_zeroChargeQuadraticPhaseTerms_le (N : Nat) [NeZero N] :
    (zeroChargeQuadraticPhaseTerms N).card ≤ 2 * N := by
  classical
  let encode :
      {term : QuadraticPhaseTerm N // quadraticPhaseCharge term = 0} →
        Lattice.Site N × Fin 2 :=
    fun term => (term.1.1 0, term.1.2.1)
  have hencode : Function.Injective encode := by
    intro left right heq
    apply Subtype.ext
    apply zeroCharge_term_eq_of_mode_zero_sign_zero_eq left.2 right.2
    · exact congrArg Prod.fst heq
    · exact congrArg Prod.snd heq
  have hcard := Fintype.card_le_of_injective encode hencode
  calc
    (zeroChargeQuadraticPhaseTerms N).card =
        (Finset.univ.subtype fun term : QuadraticPhaseTerm N =>
          quadraticPhaseCharge term = 0).card := by
      rw [Finset.card_subtype]
      rfl
    _ = Fintype.card
        {term : QuadraticPhaseTerm N // quadraticPhaseCharge term = 0} := by
      simp
    _ ≤ Fintype.card (Lattice.Site N × Fin 2) := hcard
    _ = 2 * N := by simp [ZMod.card, Nat.mul_comm]

/-- Exact cardinality of the exceptional zero-charge fiber. -/
theorem card_zeroChargeQuadraticPhaseTerms (N : Nat) [NeZero N] :
    (zeroChargeQuadraticPhaseTerms N).card = 2 * N := by
  classical
  let embed : Lattice.Site N × Fin 2 →
      {term : QuadraticPhaseTerm N // quadraticPhaseCharge term = 0} :=
    fun pair =>
      ⟨zeroChargeQuadraticPhaseTerm pair.1 pair.2,
        quadraticPhaseCharge_zeroChargeQuadraticPhaseTerm pair.1 pair.2⟩
  have hembed : Function.Injective embed := by
    intro left right heq
    have hterm := congrArg Subtype.val heq
    apply Prod.ext
    · exact congrArg (fun term : QuadraticPhaseTerm N => term.1 0) hterm
    · exact congrArg (fun term : QuadraticPhaseTerm N => term.2.1) hterm
  have hlower := Fintype.card_le_of_injective embed hembed
  apply Nat.le_antisymm (card_zeroChargeQuadraticPhaseTerms_le N)
  calc
    2 * N = Fintype.card (Lattice.Site N × Fin 2) := by
      simp [ZMod.card, Nat.mul_comm]
    _ ≤ Fintype.card
        {term : QuadraticPhaseTerm N // quadraticPhaseCharge term = 0} :=
      hlower
    _ = (zeroChargeQuadraticPhaseTerms N).card := by
      rw [zeroChargeQuadraticPhaseTerms]
      rw [← Finset.card_subtype
        (fun term : QuadraticPhaseTerm N => quadraticPhaseCharge term = 0)
        Finset.univ]
      simp

/-- For the physical quadratic coupling and prescribed-energy radii, the
acoustic cubic-vertex estimate removes both repeated input frequencies from
the norm square of a zero-charge term. -/
theorem normSq_physical_zeroChargeDuhamelCoefficient_le
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (energyBound : Real) (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    (term : QuadraticPhaseTerm N)
    (hzero : quadraticPhaseCharge term = 0) :
    Complex.normSq
        (freeQuadraticDuhamelCoefficient
          (physicalQuadraticCoupling kappa g m observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) term) ≤
      (kappa * g) ^ 2 * modeFrequency m observed * energyBound ^ 2 / 8 := by
  have hstructure :=
    (quadraticPhaseCharge_eq_zero_iff_repeated_opposite term).1 hzero
  by_cases hpositive : PositiveModeTuple m
      (quadraticCollisionModes observed term)
  · have hfrequencyChild : 0 < modeFrequency m (term.1 0) := by
      simpa only [quadraticCollisionModes, Fin.cons_succ] using
        hpositive (Fin.succ (0 : Fin 2))
    have hfrequencyObserved : 0 < modeFrequency m observed := by
      simpa only [quadraticCollisionModes, Fin.cons_zero] using
        hpositive (0 : Fin 3)
    rw [normSq_physicalQuadraticDuhamelCoefficient_eq
      kappa g m observed energy term (fun r => henergy _) hpositive]
    have hactionNonneg : 0 ≤ ∏ r : Fin 2,
        modeAction energy (modeFrequency m) (term.1 r) := by
      apply Finset.prod_nonneg
      intro r _hr
      exact div_nonneg (henergy _)
        (modeFrequency_nonneg m _)
    have hweight := normalizedInteractionWeight_three_le
      m (quadraticCollisionModes observed term) hpositive
    have hindexOne : (1 : Fin 3) = Fin.succ (0 : Fin 2) := rfl
    have hindexTwo : (2 : Fin 3) = Fin.succ (1 : Fin 2) := rfl
    rw [quadraticCollisionModes, Fin.cons_zero, hindexOne, Fin.cons_succ,
      hindexTwo, Fin.cons_succ] at hweight
    calc
      (kappa * g) ^ 2 *
          normalizedInteractionWeight m
            (quadraticCollisionModes observed term) *
          ∏ r : Fin 2,
            modeAction energy (modeFrequency m) (term.1 r) ≤
        (kappa * g) ^ 2 *
          (modeFrequency m observed * modeFrequency m (term.1 0) *
            modeFrequency m (term.1 1) / 8) *
          ∏ r : Fin 2,
            modeAction energy (modeFrequency m) (term.1 r) := by
        apply mul_le_mul_of_nonneg_right _ hactionNonneg
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact hweight
      _ = (kappa * g) ^ 2 * modeFrequency m observed *
          energy (term.1 0) ^ 2 / 8 := by
        simp only [Fin.prod_univ_two, modeAction]
        rw [← hstructure.1]
        field_simp [hfrequencyChild.ne']
      _ ≤ (kappa * g) ^ 2 * modeFrequency m observed *
          energyBound ^ 2 / 8 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (henergy _) henergyBoundNonneg).2
            (henergyBound _))
          (mul_nonneg (sq_nonneg _) (modeFrequency_nonneg m observed))
  · rw [freeQuadraticDuhamelCoefficient_eq_zero_of_not_positive
      (physicalQuadraticCoupling kappa g m observed) m observed
      (phaseEnergyRadius energy (modeFrequency m)) term hpositive]
    simp only [Complex.normSq_zero]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (sq_nonneg _) (modeFrequency_nonneg m observed))
        (sq_nonneg _)) (by norm_num)

/-- Norm form of the physical zero-charge coefficient bound. -/
theorem norm_physical_zeroChargeDuhamelCoefficient_le
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (energyBound : Real) (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    (term : QuadraticPhaseTerm N)
    (hzero : quadraticPhaseCharge term = 0) :
    ‖freeQuadraticDuhamelCoefficient
        (physicalQuadraticCoupling kappa g m observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) term‖ ≤
      Real.sqrt ((kappa * g) ^ 2 * modeFrequency m observed *
        energyBound ^ 2 / 8) := by
  have hradicand : 0 ≤
      (kappa * g) ^ 2 * modeFrequency m observed * energyBound ^ 2 / 8 := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (sq_nonneg _) (modeFrequency_nonneg m observed))
        (sq_nonneg _)) (by norm_num)
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
  rw [Complex.sq_norm, Real.sq_sqrt hradicand]
  exact normSq_physical_zeroChargeDuhamelCoefficient_le
    kappa g m observed energy energyBound henergyBoundNonneg
    henergy henergyBound term hzero

/-- A termwise coefficient bound controls the complete zero-charge
cross-orbit coefficient with its explicit finite-volume multiplicity. -/
theorem norm_freeQuadraticZeroChargeCrossOrbitCoefficient_le_volume
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    (coefficientBound : Real) (hboundNonneg : 0 ≤ coefficientBound)
    (hcoefficient : ∀ term : QuadraticPhaseTerm N,
      quadraticPhaseCharge term = 0 →
      ‖freeQuadraticDuhamelCoefficient
        coupling m observed radius term‖ ≤ coefficientBound) :
    ‖freeQuadraticZeroChargeCrossOrbitCoefficient
        coupling m observed radius‖ ≤
      ((2 * N : Nat) : Real) ^ 2 * coefficientBound ^ 2 := by
  classical
  unfold freeQuadraticZeroChargeCrossOrbitCoefficient
  calc
    ‖∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        if quadraticPhaseCharge left = 0 ∧
            quadraticPhaseCharge right = 0 ∧
            right ∉ quadraticSwapOrbit left then
          freeQuadraticDuhamelCoefficient coupling m observed radius left *
            starRingEnd Complex
              (freeQuadraticDuhamelCoefficient
                coupling m observed radius right)
        else 0‖ ≤
      ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        ‖if quadraticPhaseCharge left = 0 ∧
            quadraticPhaseCharge right = 0 ∧
            right ∉ quadraticSwapOrbit left then
          freeQuadraticDuhamelCoefficient coupling m observed radius left *
            starRingEnd Complex
              (freeQuadraticDuhamelCoefficient
                coupling m observed radius right)
        else 0‖ :=
      (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun _left _hleft => norm_sum_le _ _)
    _ ≤ ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        if quadraticPhaseCharge left = 0 ∧
            quadraticPhaseCharge right = 0 then
          coefficientBound ^ 2
        else 0 := by
      apply Finset.sum_le_sum
      intro left _hleft
      apply Finset.sum_le_sum
      intro right _hright
      by_cases hkeep : quadraticPhaseCharge left = 0 ∧
          quadraticPhaseCharge right = 0 ∧
          right ∉ quadraticSwapOrbit left
      · rw [if_pos hkeep, if_pos ⟨hkeep.1, hkeep.2.1⟩,
          norm_mul]
        simp only [Complex.norm_conj]
        rw [pow_two]
        exact mul_le_mul (hcoefficient left hkeep.1)
          (hcoefficient right hkeep.2.1)
          (norm_nonneg _) hboundNonneg
      · rw [if_neg hkeep]
        simp only [norm_zero]
        positivity
    _ = ((zeroChargeQuadraticPhaseTerms N).card : Real) ^ 2 *
        coefficientBound ^ 2 := by
      have hinner (left : QuadraticPhaseTerm N) :
          (∑ right : QuadraticPhaseTerm N,
            if quadraticPhaseCharge left = 0 ∧
                quadraticPhaseCharge right = 0 then
              coefficientBound ^ 2
            else 0) =
          if quadraticPhaseCharge left = 0 then
            ((zeroChargeQuadraticPhaseTerms N).card : Real) *
              coefficientBound ^ 2
          else 0 := by
        by_cases hleft : quadraticPhaseCharge left = 0
        · rw [if_pos hleft]
          simp only [hleft, true_and]
          calc
            (∑ right : QuadraticPhaseTerm N,
                if quadraticPhaseCharge right = 0 then
                  coefficientBound ^ 2
                else 0) =
              ∑ right ∈ zeroChargeQuadraticPhaseTerms N,
                coefficientBound ^ 2 := by
              rw [zeroChargeQuadraticPhaseTerms, Finset.sum_filter]
            _ = ((zeroChargeQuadraticPhaseTerms N).card : Real) *
                coefficientBound ^ 2 := by simp
        · simp [hleft]
      simp_rw [hinner]
      calc
        (∑ left : QuadraticPhaseTerm N,
          if quadraticPhaseCharge left = 0 then
            ((zeroChargeQuadraticPhaseTerms N).card : Real) *
              coefficientBound ^ 2
          else 0) =
            ∑ left ∈ zeroChargeQuadraticPhaseTerms N,
              ((zeroChargeQuadraticPhaseTerms N).card : Real) *
                coefficientBound ^ 2 := by
          rw [zeroChargeQuadraticPhaseTerms, Finset.sum_filter]
        _ = ((zeroChargeQuadraticPhaseTerms N).card : Real) ^ 2 *
            coefficientBound ^ 2 := by
          simp [pow_two]
          ring
    _ ≤ ((2 * N : Nat) : Real) ^ 2 * coefficientBound ^ 2 := by
      gcongr
      exact_mod_cast card_zeroChargeQuadraticPhaseTerms_le N

/-- Explicit fixed-time bound for the real cross-orbit remainder.  Its only
volume dependence is the displayed zero-charge fiber multiplicity. -/
theorem abs_re_freeQuadraticCrossSwapOrbitCoherentRemainder_le_volume
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {time : Real}
    (coefficientBound : Real) (hboundNonneg : 0 ≤ coefficientBound)
    (hcoefficient : ∀ term : QuadraticPhaseTerm N,
      quadraticPhaseCharge term = 0 →
      ‖freeQuadraticDuhamelCoefficient
        coupling m observed radius term‖ ≤ coefficientBound)
    (hfrequency : 0 < frequency observed) (htime : 0 < time) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        coupling m observed radius frequency time).re| ≤
      (((2 * N : Nat) : Real) ^ 2 * coefficientBound ^ 2) *
        (4 / (frequency observed ^ 2 * time)) := by
  exact (abs_re_freeQuadraticCrossSwapOrbitCoherentRemainder_le_inverseTime
    coupling m observed radius frequency hfrequency htime).trans
      (mul_le_mul_of_nonneg_right
        (norm_freeQuadraticZeroChargeCrossOrbitCoefficient_le_volume
          coupling m observed radius coefficientBound hboundNonneg
          hcoefficient)
        (by positivity))

/-- Substituting the physical coupling, prescribed-energy radii, and the
acoustic cubic-vertex bound gives the strongest deterministic estimate
available from the current library.  At a uniform per-mode energy ceiling it
is a quadratic-in-volume upper bound of order `N^2`; no localization or
random cancellation has been used. -/
theorem abs_re_physical_crossOrbit_le_energy_volume
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (energyBound : Real) (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (hfrequency : 0 < modeFrequency m observed)
    (htime : 0 < time) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time).re| ≤
      2 * (N : Real) ^ 2 * (kappa * g) ^ 2 * energyBound ^ 2 /
        (modeFrequency m observed * time) := by
  have hradicand : 0 ≤
      (kappa * g) ^ 2 * modeFrequency m observed * energyBound ^ 2 / 8 := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (sq_nonneg _) (modeFrequency_nonneg m observed))
        (sq_nonneg _)) (by norm_num)
  calc
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time).re| ≤
      (((2 * N : Nat) : Real) ^ 2 *
          (Real.sqrt ((kappa * g) ^ 2 * modeFrequency m observed *
            energyBound ^ 2 / 8)) ^ 2) *
        (4 / (modeFrequency m observed ^ 2 * time)) :=
      abs_re_freeQuadraticCrossSwapOrbitCoherentRemainder_le_volume
        (physicalQuadraticCoupling kappa g m observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        (Real.sqrt ((kappa * g) ^ 2 * modeFrequency m observed *
          energyBound ^ 2 / 8)) (Real.sqrt_nonneg _)
        (fun term hzero =>
          norm_physical_zeroChargeDuhamelCoefficient_le
            kappa g m observed energy energyBound henergyBoundNonneg
            henergy henergyBound term hzero)
        hfrequency htime
    _ = 2 * (N : Real) ^ 2 * (kappa * g) ^ 2 * energyBound ^ 2 /
        (modeFrequency m observed * time) := by
      rw [Real.sq_sqrt hradicand]
      push_cast
      field_simp [hfrequency.ne', htime.ne']
      ring

/-- After the natural `N^2` normalization, the preceding deterministic
energy bound is genuinely volume-uniform provided the observed mode stays
above a fixed positive frequency floor. -/
theorem normalized_abs_re_physical_crossOrbit_le_energy
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (energyBound frequencyFloor : Real)
    (henergyBoundNonneg : 0 ≤ energyBound)
    (hfrequencyFloor : 0 < frequencyFloor)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (hfrequency : frequencyFloor ≤ modeFrequency m observed)
    (htime : 0 < time) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time).re| / (N : Real) ^ 2 ≤
      2 * (kappa * g) ^ 2 * energyBound ^ 2 /
        (frequencyFloor * time) := by
  have hN : (0 : Real) < N := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hfrequencyObserved : 0 < modeFrequency m observed :=
    hfrequencyFloor.trans_le hfrequency
  calc
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time).re| / (N : Real) ^ 2 ≤
      (2 * (N : Real) ^ 2 * (kappa * g) ^ 2 * energyBound ^ 2 /
        (modeFrequency m observed * time)) / (N : Real) ^ 2 :=
      div_le_div_of_nonneg_right
        (abs_re_physical_crossOrbit_le_energy_volume
          kappa g m observed energy energyBound henergyBoundNonneg
          henergy henergyBound hfrequencyObserved htime)
        (sq_nonneg _)
    _ = 2 * (kappa * g) ^ 2 * energyBound ^ 2 /
        (modeFrequency m observed * time) := by
      field_simp [hN.ne', hfrequencyObserved.ne', htime.ne']
    _ ≤ 2 * (kappa * g) ^ 2 * energyBound ^ 2 /
        (frequencyFloor * time) := by
      have hnumerator : 0 ≤
          2 * (kappa * g) ^ 2 * energyBound ^ 2 := by positivity
      have hdenominatorFloor : 0 < frequencyFloor * time :=
        mul_pos hfrequencyFloor htime
      apply div_le_div_of_nonneg_left hnumerator hdenominatorFloor
      exact mul_le_mul_of_nonneg_right hfrequency htime.le

/-- Transparent sufficient condition for an `N`-uniform `O(T⁻¹)` bound.
It isolates the two genuinely missing uniform inputs: `1/N` decay of each
zero-charge term coefficient and a volume-uniform positive lower bound on the
observed frequency. -/
theorem abs_re_crossOrbit_le_of_inverseVolumeCoefficient
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {time : Real}
    (uniformCoefficient frequencyFloor : Real)
    (huniformCoefficient : 0 ≤ uniformCoefficient)
    (hfrequencyFloor : 0 < frequencyFloor)
    (hcoefficient : ∀ term : QuadraticPhaseTerm N,
      quadraticPhaseCharge term = 0 →
      ‖freeQuadraticDuhamelCoefficient
        coupling m observed radius term‖ ≤ uniformCoefficient / N)
    (hfrequency : frequencyFloor ≤ frequency observed)
    (htime : 0 < time) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        coupling m observed radius frequency time).re| ≤
      16 * uniformCoefficient ^ 2 / (frequencyFloor ^ 2 * time) := by
  have hN : (0 : Real) < N := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hcoefficientBoundNonneg :
      0 ≤ uniformCoefficient / (N : Real) :=
    div_nonneg huniformCoefficient hN.le
  have hfrequencyObserved : 0 < frequency observed :=
    hfrequencyFloor.trans_le hfrequency
  calc
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        coupling m observed radius frequency time).re| ≤
      (((2 * N : Nat) : Real) ^ 2 *
          (uniformCoefficient / (N : Real)) ^ 2) *
        (4 / (frequency observed ^ 2 * time)) :=
      abs_re_freeQuadraticCrossSwapOrbitCoherentRemainder_le_volume
        coupling m observed radius frequency
        (uniformCoefficient / (N : Real)) hcoefficientBoundNonneg
        hcoefficient hfrequencyObserved htime
    _ = 16 * uniformCoefficient ^ 2 /
        (frequency observed ^ 2 * time) := by
      push_cast
      field_simp [hN.ne', hfrequencyObserved.ne', htime.ne']
      ring
    _ ≤ 16 * uniformCoefficient ^ 2 /
        (frequencyFloor ^ 2 * time) := by
      have hnumerator : 0 ≤ 16 * uniformCoefficient ^ 2 := by positivity
      have hdenominatorFloor : 0 < frequencyFloor ^ 2 * time :=
        mul_pos (sq_pos_of_pos hfrequencyFloor) htime
      apply div_le_div_of_nonneg_left hnumerator hdenominatorFloor
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ hfrequencyFloor.le hfrequencyObserved.le).2 hfrequency)
        htime.le

end

end ArchonPhysics.FreeFPUTCrossOrbitCoefficientVolumeBound
