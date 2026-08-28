import ArchonPhysics.FreeFPUTCrossOrbitCoefficientVolumeBound
import ArchonPhysics.RepeatedParentChildAcousticCumulativeBound

/-!
# Linear-volume bound for the free FPUT zero-charge cross orbit

The earlier cardinality argument treats every ordered zero-charge pair
separately and therefore gives an `O(N^2 / T)` bound.  Here the repeated-child
geometry is retained.  For a fixed observed ordered mode `q`, the normalized
edge frame satisfies the unconditional fixed-child Bessel estimate

`sum_k (sum_j u k j ^ 2 * u q j) ^ 2 <= 1`.

After Cauchy--Schwarz over the `N` repeated child labels, the complete
zero-charge `l1` coefficient mass is only `O(sqrt N)`.  Squaring it controls
every cross-orbit ordered pair by `O(N)`.  Random phases cannot improve this
step because all these terms have zero Haar charge.  No localization,
small-denominator density, or independence of spectral coefficients is used.
-/

namespace ArchonPhysics.FreeFPUTCrossOrbitLinearVolumeBound

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTCrossOrbitCoefficientVolumeBound
open ArchonPhysics.FreeFPUTCrossOrbitRealDecay
open ArchonPhysics.FreeFPUTCrossOrbitZeroChargeBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RepeatedModeTupleInteractionBound
open ArchonPhysics.RepeatedParentChildAcousticCumulativeBound
open ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder

noncomputable section

/-- The exact parametrization of the zero-charge fiber by one repeated mode
and the first of the two opposite binary signs. -/
def zeroChargeQuadraticPhaseTermEquiv
    {N : Nat} [NeZero N] :
    Lattice.Site N × Fin 2 ≃
      {term : QuadraticPhaseTerm N // quadraticPhaseCharge term = 0} where
  toFun pair :=
    ⟨zeroChargeQuadraticPhaseTerm pair.1 pair.2,
      quadraticPhaseCharge_zeroChargeQuadraticPhaseTerm pair.1 pair.2⟩
  invFun term := (term.1.1 0, term.1.2.1)
  left_inv pair := by
    apply Prod.ext <;> rfl
  right_inv term := by
    apply Subtype.ext
    apply zeroCharge_term_eq_of_mode_zero_sign_zero_eq
      (quadraticPhaseCharge_zeroChargeQuadraticPhaseTerm
        (term.1.1 0) term.1.2.1) term.2 <;> rfl

/-- Reindex any sum supported on zero charge by its exact `mode × sign`
parametrization. -/
theorem sum_ite_quadraticPhaseCharge_eq_zero
    {N : Nat} [NeZero N] (f : QuadraticPhaseTerm N → Real) :
    (∑ term : QuadraticPhaseTerm N,
        if quadraticPhaseCharge term = 0 then f term else 0) =
      ∑ mode : Lattice.Site N, ∑ sign : Fin 2,
        f (zeroChargeQuadraticPhaseTerm mode sign) := by
  classical
  calc
    (∑ term : QuadraticPhaseTerm N,
        if quadraticPhaseCharge term = 0 then f term else 0) =
        ∑ term : {term : QuadraticPhaseTerm N //
          quadraticPhaseCharge term = 0}, f term.1 := by
      rw [← Finset.sum_filter]
      simpa using (Finset.sum_subtype
        (p := fun term : QuadraticPhaseTerm N ↦ quadraticPhaseCharge term = 0)
        (Finset.univ.filter fun term : QuadraticPhaseTerm N ↦
          quadraticPhaseCharge term = 0) (by simp) f)
    _ = ∑ pair : Lattice.Site N × Fin 2,
        f (zeroChargeQuadraticPhaseTerm pair.1 pair.2) := by
      symm
      exact Equiv.sum_comp zeroChargeQuadraticPhaseTermEquiv
        (fun term ↦ f term.1)
    _ = ∑ mode : Lattice.Site N, ∑ sign : Fin 2,
        f (zeroChargeQuadraticPhaseTerm mode sign) := by
      exact Fintype.sum_prod_type _

/-- Binary phase labels do not enter the deterministic coefficient: within
one repeated child mode the two zero-charge terms have identical amplitude. -/
theorem freeQuadraticDuhamelCoefficient_zeroCharge_sign_independent
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed mode : Lattice.Site N) (radius : Lattice.Site N → Real)
    (leftSign rightSign : Fin 2) :
    freeQuadraticDuhamelCoefficient coupling m observed radius
        (zeroChargeQuadraticPhaseTerm mode leftSign) =
      freeQuadraticDuhamelCoefficient coupling m observed radius
        (zeroChargeQuadraticPhaseTerm mode rightSign) := by
  unfold freeQuadraticDuhamelCoefficient quadraticPhaseCoefficient
    zeroChargeQuadraticPhaseTerm
  rfl

/-- One ordered repeated-child zero-charge coefficient retains the exact
edge-frame cubic factor.  The only spectral input is simplicity, used to
identify the canonical squared projector weight with the physical normal-mode
coefficient. -/
theorem normSq_physical_orderedZeroChargeDuhamelCoefficient_le_frame
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (q k : OrderedModeIndex N) (sign : Fin 2)
    (energy : Lattice.Site N → Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (henergy : ∀ mode, 0 ≤ energy mode) :
    Complex.normSq
        (freeQuadraticDuhamelCoefficient
          (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
          m (orderedIndexEquiv q)
          (phaseEnergyRadius energy (modeFrequency m))
          (zeroChargeQuadraticPhaseTerm
            (orderedIndexEquiv k) sign)) ≤
      (kappa * g) ^ 2 *
          orderedModeFrequency (harmonicHermitian m) q *
          energy (orderedIndexEquiv k) ^ 2 *
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) k q ^ 2 / 8 := by
  let modes : OrderedModeTriple N := ![q, k, k]
  let term : QuadraticPhaseTerm N :=
    zeroChargeQuadraticPhaseTerm (orderedIndexEquiv k) sign
  have htermModes :
      quadraticCollisionModes (orderedIndexEquiv q) term =
        fun r ↦ orderedIndexEquiv (modes r) := by
    funext r
    fin_cases r <;> rfl
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · have hphysical : PositiveModeTuple m
        (fun r ↦ orderedIndexEquiv (modes r)) :=
      (isPositiveOrderedTriple_iff_physical m modes).1 hpositive
    have hkfreq : 0 < orderedModeFrequency (harmonicHermitian m) k := by
      simpa [modes, IsPositiveOrderedTriple] using hpositive (1 : Fin 3)
    have hqfreq : 0 < orderedModeFrequency (harmonicHermitian m) q := by
      simpa [modes, IsPositiveOrderedTriple] using hpositive (0 : Fin 3)
    have hkactive0 := harmonicActiveNormalizedCoefficient_nonneg m k
    have hqactive0 := harmonicActiveNormalizedCoefficient_nonneg m q
    have hkactive := abs_activeOrderedEigenvalue_mul_inv_two_frequency_le m k
    have hqactive := abs_activeOrderedEigenvalue_mul_inv_two_frequency_le m q
    change |harmonicActiveNormalizedCoefficient m k| ≤
      orderedModeFrequency (harmonicHermitian m) k / 2 at hkactive
    change |harmonicActiveNormalizedCoefficient m q| ≤
      orderedModeFrequency (harmonicHermitian m) q / 2 at hqactive
    rw [abs_of_nonneg hkactive0] at hkactive
    rw [abs_of_nonneg hqactive0] at hqactive
    have hweight : harmonicOrderedNormalizedInteractionWeight m modes ≤
        (orderedModeFrequency (harmonicHermitian m) k / 2) ^ 2 *
          (orderedModeFrequency (harmonicHermitian m) q / 2) *
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) k q ^ 2 := by
      change harmonicOrderedNormalizedInteractionWeight m ![q, k, k] ≤ _
      rw [harmonicOrderedNormalizedInteractionWeight_repeated_one_two_eq,
        harmonicOrderedNormalizedInteractionWeight_repeated_zero_one_eq]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (pow_le_pow_left₀ hkactive0 hkactive 2)
          hqactive hqactive0 (sq_nonneg _)) (sq_nonneg _)
    have haction : 0 ≤ ∏ r : Fin 2,
        modeAction energy (modeFrequency m)
          ((zeroChargeQuadraticPhaseTerm
            (orderedIndexEquiv k) sign).1 r) := by
      apply Finset.prod_nonneg
      intro r _hr
      exact div_nonneg (henergy _) (modeFrequency_nonneg m _)
    rw [normSq_physicalQuadraticDuhamelCoefficient_eq
      kappa g m (orderedIndexEquiv q) energy term
      (fun r ↦ henergy _) (by simpa [htermModes] using hphysical)]
    rw [htermModes, ← harmonicOrderedNormalizedInteractionWeight_eq
      m hsimple modes]
    calc
      (kappa * g) ^ 2 * harmonicOrderedNormalizedInteractionWeight m modes *
          ∏ r : Fin 2,
            modeAction energy (modeFrequency m)
              ((zeroChargeQuadraticPhaseTerm
                (orderedIndexEquiv k) sign).1 r) ≤
        (kappa * g) ^ 2 *
            ((orderedModeFrequency (harmonicHermitian m) k / 2) ^ 2 *
              (orderedModeFrequency (harmonicHermitian m) q / 2) *
              repeatedCubicCoefficient
                (harmonicNormalizedEdgeFrame m) k q ^ 2) *
          ∏ r : Fin 2,
            modeAction energy (modeFrequency m)
              ((zeroChargeQuadraticPhaseTerm
                (orderedIndexEquiv k) sign).1 r) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hweight (sq_nonneg _)) haction
      _ = (kappa * g) ^ 2 *
          orderedModeFrequency (harmonicHermitian m) q *
          energy (orderedIndexEquiv k) ^ 2 *
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) k q ^ 2 / 8 := by
        simp only [Fin.prod_univ_two, zeroChargeQuadraticPhaseTerm,
          modeAction]
        rw [← orderedModeFrequency_harmonicHermitian_eq m k]
        field_simp [hkfreq.ne']
        ring
  · have hphysical : ¬ PositiveModeTuple m
        (quadraticCollisionModes (orderedIndexEquiv q) term) := by
      intro hp
      apply hpositive
      apply (isPositiveOrderedTriple_iff_physical m modes).2
      rw [← htermModes]
      exact hp
    rw [freeQuadraticDuhamelCoefficient_eq_zero_of_not_positive
      (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
      m (orderedIndexEquiv q)
      (phaseEnergyRadius energy (modeFrequency m)) term hphysical]
    simp only [Complex.normSq_zero]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (sq_nonneg _)
            (Real.sqrt_nonneg _))
          (sq_nonneg _))
        (sq_nonneg _)) (by norm_num)

/-- Canonical representative of the two identical zero-charge sign sectors
for one ordered repeated child. -/
def physicalOrderedZeroChargeDuhamelCoefficient
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (q k : OrderedModeIndex N) (energy : Lattice.Site N → Real) : Complex :=
  freeQuadraticDuhamelCoefficient
    (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
    m (orderedIndexEquiv q)
    (phaseEnergyRadius energy (modeFrequency m))
    (zeroChargeQuadraticPhaseTerm (orderedIndexEquiv k) 0)

/-- Fixed-child Bessel summation removes the apparent sum over repeated child
modes from the squared coefficient mass. -/
theorem sum_sq_norm_physicalOrderedZeroChargeDuhamelCoefficient_le
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound) :
    (∑ k : OrderedModeIndex N,
        ‖physicalOrderedZeroChargeDuhamelCoefficient
          kappa g m q k energy‖ ^ 2) ≤
      (kappa * g) ^ 2 *
        orderedModeFrequency (harmonicHermitian m) q *
        energyBound ^ 2 / 8 := by
  let A := (kappa * g) ^ 2 *
    orderedModeFrequency (harmonicHermitian m) q / 8
  have hA : 0 ≤ A := by
    exact div_nonneg
      (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)) (by norm_num)
  calc
    (∑ k : OrderedModeIndex N,
        ‖physicalOrderedZeroChargeDuhamelCoefficient
          kappa g m q k energy‖ ^ 2) =
        ∑ k : OrderedModeIndex N,
          Complex.normSq
            (physicalOrderedZeroChargeDuhamelCoefficient
              kappa g m q k energy) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact Complex.sq_norm _
    _ ≤ ∑ k : OrderedModeIndex N,
        A * energy (orderedIndexEquiv k) ^ 2 *
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) k q ^ 2 := by
      apply Finset.sum_le_sum
      intro k _hk
      have hkbound :=
        normSq_physical_orderedZeroChargeDuhamelCoefficient_le_frame
          kappa g m q k 0 energy hsimple henergy
      change Complex.normSq
          (physicalOrderedZeroChargeDuhamelCoefficient
            kappa g m q k energy) ≤ _
      rw [show A * energy (orderedIndexEquiv k) ^ 2 *
          repeatedCubicCoefficient
              (harmonicNormalizedEdgeFrame m) k q ^ 2 =
          (kappa * g) ^ 2 *
              orderedModeFrequency (harmonicHermitian m) q *
              energy (orderedIndexEquiv k) ^ 2 *
              repeatedCubicCoefficient
                (harmonicNormalizedEdgeFrame m) k q ^ 2 / 8 by
        simp only [A]; ring]
      simpa [physicalOrderedZeroChargeDuhamelCoefficient] using hkbound
    _ ≤ ∑ k : OrderedModeIndex N,
        A * energyBound ^ 2 *
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) k q ^ 2 := by
      apply Finset.sum_le_sum
      intro k _hk
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (henergy _) henergyBoundNonneg).2
            (henergyBound _)) hA)
        (sq_nonneg _)
    _ = A * energyBound ^ 2 *
        (∑ k : OrderedModeIndex N,
          repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) k q ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ A * energyBound ^ 2 := by
      have hbessel := sum_repeatedCubicCoefficient_sq_fixed_child_le_one
        (harmonicNormalizedEdgeFrame m) (by simp [Lattice.Site])
        (harmonicNormalizedEdgeFrame_orthonormal_unconditional m) q
      simpa using mul_le_mul_of_nonneg_left hbessel
        (mul_nonneg hA (sq_nonneg _))
    _ = (kappa * g) ^ 2 *
        orderedModeFrequency (harmonicHermitian m) q *
        energyBound ^ 2 / 8 := by
      simp only [A]
      ring

/-- The exact two-sign zero-charge `l1` coefficient mass is twice the sum
over repeated child modes. -/
theorem sum_zeroCharge_norm_eq_two_mul_orderedModeSum
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real) :
    (∑ term : QuadraticPhaseTerm N,
        if quadraticPhaseCharge term = 0 then
          ‖freeQuadraticDuhamelCoefficient
            (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
            m (orderedIndexEquiv q)
            (phaseEnergyRadius energy (modeFrequency m)) term‖
        else 0) =
      2 * ∑ k : OrderedModeIndex N,
        ‖physicalOrderedZeroChargeDuhamelCoefficient
          kappa g m q k energy‖ := by
  rw [sum_ite_quadraticPhaseCharge_eq_zero]
  calc
    (∑ mode : Lattice.Site N, ∑ sign : Fin 2,
      ‖freeQuadraticDuhamelCoefficient
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
        m (orderedIndexEquiv q)
        (phaseEnergyRadius energy (modeFrequency m))
        (zeroChargeQuadraticPhaseTerm mode sign)‖) =
      ∑ k : OrderedModeIndex N,
        2 * ‖physicalOrderedZeroChargeDuhamelCoefficient
          kappa g m q k energy‖ := by
      apply Fintype.sum_equiv orderedIndexEquiv.symm
      intro mode
      rw [Fin.sum_univ_two]
      simp only [physicalOrderedZeroChargeDuhamelCoefficient]
      rw [freeQuadraticDuhamelCoefficient_zeroCharge_sign_independent
          _ m _ mode _ 1 0]
      simp only [Equiv.apply_symm_apply]
      ring
    _ = 2 * ∑ k : OrderedModeIndex N,
        ‖physicalOrderedZeroChargeDuhamelCoefficient
          kappa g m q k energy‖ := by
      rw [Finset.mul_sum]

set_option maxHeartbeats 800000 in
-- Expanding the two nested finite zero-charge sums requires extra elaboration budget.
/-- The cross-orbit coefficient is bounded by the square of the complete
zero-charge `l1` coefficient mass.  Keeping the cross selector can only reduce
the triangle bound. -/
theorem norm_freeQuadraticZeroChargeCrossOrbitCoefficient_le_sq_normMass
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real) :
    ‖freeQuadraticZeroChargeCrossOrbitCoefficient
        coupling m observed radius‖ ≤
      (∑ term : QuadraticPhaseTerm N,
        if quadraticPhaseCharge term = 0 then
          ‖freeQuadraticDuhamelCoefficient
            coupling m observed radius term‖
        else 0) ^ 2 := by
  classical
  let a : QuadraticPhaseTerm N → Real := fun term ↦
    if quadraticPhaseCharge term = 0 then
      ‖freeQuadraticDuhamelCoefficient coupling m observed radius term‖
    else 0
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
        (Finset.sum_le_sum fun _left _hleft ↦ norm_sum_le _ _)
    _ ≤ ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
        a left * a right := by
      apply Finset.sum_le_sum
      intro left _hleft
      apply Finset.sum_le_sum
      intro right _hright
      by_cases hkeep : quadraticPhaseCharge left = 0 ∧
          quadraticPhaseCharge right = 0 ∧
          right ∉ quadraticSwapOrbit left
      · rw [if_pos hkeep, norm_mul]
        simp only [Complex.norm_conj]
        simp [a, hkeep.1, hkeep.2.1]
      · rw [if_neg hkeep, norm_zero]
        apply mul_nonneg
        · by_cases hleftZero : quadraticPhaseCharge left = 0 <;>
            simp [a, hleftZero]
        · by_cases hrightZero : quadraticPhaseCharge right = 0 <;>
            simp [a, hrightZero]
    _ = (∑ term : QuadraticPhaseTerm N, a term) ^ 2 := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro left _hleft
      rw [Finset.mul_sum]
    _ = (∑ term : QuadraticPhaseTerm N,
        if quadraticPhaseCharge term = 0 then
          ‖freeQuadraticDuhamelCoefficient
            coupling m observed radius term‖
        else 0) ^ 2 := by rfl

/-- Main deterministic improvement: for a simple spectrum and a uniform
per-mode energy ceiling, the complete physical zero-charge cross coefficient
is only linear in the volume. -/
theorem norm_physical_zeroChargeCrossOrbitCoefficient_le_linearVolume
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound) :
    ‖freeQuadraticZeroChargeCrossOrbitCoefficient
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
        m (orderedIndexEquiv q)
        (phaseEnergyRadius energy (modeFrequency m))‖ ≤
      (N : Real) * (kappa * g) ^ 2 *
        orderedModeFrequency (harmonicHermitian m) q *
        energyBound ^ 2 / 2 := by
  let S := ∑ k : OrderedModeIndex N,
    ‖physicalOrderedZeroChargeDuhamelCoefficient kappa g m q k energy‖
  have hsumSq :
      (∑ k : OrderedModeIndex N,
        ‖physicalOrderedZeroChargeDuhamelCoefficient
          kappa g m q k energy‖ ^ 2) ≤
        (kappa * g) ^ 2 *
          orderedModeFrequency (harmonicHermitian m) q *
          energyBound ^ 2 / 8 :=
    sum_sq_norm_physicalOrderedZeroChargeDuhamelCoefficient_le
      kappa g m q energy energyBound hsimple henergyBoundNonneg
      henergy henergyBound
  have hcauchy : S ^ 2 ≤
      (N : Real) * ∑ k : OrderedModeIndex N,
        ‖physicalOrderedZeroChargeDuhamelCoefficient
          kappa g m q k energy‖ ^ 2 := by
    simpa [S, Lattice.Site] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (OrderedModeIndex N)))
        (f := fun k ↦
          ‖physicalOrderedZeroChargeDuhamelCoefficient
            kappa g m q k energy‖))
  have hNnonneg : (0 : Real) ≤ N := by positivity
  calc
    ‖freeQuadraticZeroChargeCrossOrbitCoefficient
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
        m (orderedIndexEquiv q)
        (phaseEnergyRadius energy (modeFrequency m))‖ ≤
      (∑ term : QuadraticPhaseTerm N,
        if quadraticPhaseCharge term = 0 then
          ‖freeQuadraticDuhamelCoefficient
            (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
            m (orderedIndexEquiv q)
            (phaseEnergyRadius energy (modeFrequency m)) term‖
        else 0) ^ 2 :=
      norm_freeQuadraticZeroChargeCrossOrbitCoefficient_le_sq_normMass
        _ m _ _
    _ = (2 * S) ^ 2 := by
      rw [sum_zeroCharge_norm_eq_two_mul_orderedModeSum]
    _ = 4 * S ^ 2 := by ring
    _ ≤ 4 * ((N : Real) *
        ∑ k : OrderedModeIndex N,
          ‖physicalOrderedZeroChargeDuhamelCoefficient
            kappa g m q k energy‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hcauchy (by norm_num)
    _ ≤ 4 * ((N : Real) *
        ((kappa * g) ^ 2 *
          orderedModeFrequency (harmonicHermitian m) q *
          energyBound ^ 2 / 8)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsumSq hNnonneg) (by norm_num)
    _ = (N : Real) * (kappa * g) ^ 2 *
        orderedModeFrequency (harmonicHermitian m) q *
        energyBound ^ 2 / 2 := by ring

/-- The physical cross-orbit real remainder is `O(N/T)`, improving the raw
zero-charge-cardinality estimate `O(N^2/T)` by one full power of volume. -/
theorem abs_re_physical_crossOrbit_le_energy_linearVolume
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real}
    (hfrequency : 0 < orderedModeFrequency (harmonicHermitian m) q)
    (htime : 0 < time) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
        m (orderedIndexEquiv q)
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time).re| ≤
      2 * (N : Real) * (kappa * g) ^ 2 * energyBound ^ 2 /
        (orderedModeFrequency (harmonicHermitian m) q * time) := by
  have hphysicalFrequency :
      0 < modeFrequency m (orderedIndexEquiv q) := by
    simpa [orderedModeFrequency_harmonicHermitian_eq] using hfrequency
  have hweightNonneg : 0 ≤
      4 / (modeFrequency m (orderedIndexEquiv q) ^ 2 * time) := by
    positivity
  calc
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
        m (orderedIndexEquiv q)
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time).re| ≤
      ‖freeQuadraticZeroChargeCrossOrbitCoefficient
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
        m (orderedIndexEquiv q)
        (phaseEnergyRadius energy (modeFrequency m))‖ *
          (4 / (modeFrequency m (orderedIndexEquiv q) ^ 2 * time)) :=
      abs_re_freeQuadraticCrossSwapOrbitCoherentRemainder_le_inverseTime
        _ m _ _ _ hphysicalFrequency htime
    _ ≤ ((N : Real) * (kappa * g) ^ 2 *
          orderedModeFrequency (harmonicHermitian m) q *
          energyBound ^ 2 / 2) *
        (4 / (modeFrequency m (orderedIndexEquiv q) ^ 2 * time)) := by
      exact mul_le_mul_of_nonneg_right
        (norm_physical_zeroChargeCrossOrbitCoefficient_le_linearVolume
          kappa g m q energy energyBound hsimple henergyBoundNonneg
          henergy henergyBound) hweightNonneg
    _ = 2 * (N : Real) * (kappa * g) ^ 2 * energyBound ^ 2 /
        (orderedModeFrequency (harmonicHermitian m) q * time) := by
      rw [← orderedModeFrequency_harmonicHermitian_eq m q]
      field_simp [hfrequency.ne', htime.ne']
      ring

/-- Equivalently, after the original `N^2` normalization the cross remainder
is `O(1/(N T))`.  The observed frequency remains explicit; no acoustic gap is
silently inserted. -/
theorem normalized_abs_re_physical_crossOrbit_le_inverseVolume
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real}
    (hfrequency : 0 < orderedModeFrequency (harmonicHermitian m) q)
    (htime : 0 < time) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
        m (orderedIndexEquiv q)
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time).re| / (N : Real) ^ 2 ≤
      2 * (kappa * g) ^ 2 * energyBound ^ 2 /
        ((N : Real) *
          orderedModeFrequency (harmonicHermitian m) q * time) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  calc
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
        m (orderedIndexEquiv q)
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time).re| / (N : Real) ^ 2 ≤
      (2 * (N : Real) * (kappa * g) ^ 2 * energyBound ^ 2 /
        (orderedModeFrequency (harmonicHermitian m) q * time)) /
          (N : Real) ^ 2 :=
      div_le_div_of_nonneg_right
        (abs_re_physical_crossOrbit_le_energy_linearVolume
          kappa g m q energy energyBound hsimple henergyBoundNonneg
          henergy henergyBound hfrequency htime) (sq_nonneg _)
    _ = 2 * (kappa * g) ^ 2 * energyBound ^ 2 /
        ((N : Real) *
          orderedModeFrequency (harmonicHermitian m) q * time) := by
      field_simp [hN.ne', hfrequency.ne', htime.ne']

end

end ArchonPhysics.FreeFPUTCrossOrbitLinearVolumeBound
