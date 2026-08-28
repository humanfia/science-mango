import ArchonPhysics.FreeFPUTCrossOrbitLinearVolumeBound
import ArchonPhysics.GaussianRandomMassSimpleSpectrum
import ArchonPhysics.RandomMassHarmonicTrace
import ArchonPhysics.ConcreteGaussianTwoBandInitialEnsemble
import ArchonPhysics.OrderedSpectrumWeyl

/-!
# Gaussian frozen-mass consumer of the linear-volume cross-orbit bound

This module selects the leading ordered harmonic mode.  The compact frozen
mass support gives this mode a deterministic positive frequency floor, while
Gaussian absolute continuity makes the ordered spectrum simple almost surely.
Consequently the `N^2`-normalized cross-orbit remainder is almost surely
`O(1/N)` at every fixed positive time for uniformly bounded modal energies.
-/

namespace ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer

open ArchonPhysics
open ArchonPhysics.FreeFPUTCrossOrbitLinearVolumeBound
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.GaussianRandomMassSimpleSpectrum
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableHarmonicData
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSpectrumWeyl
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassHarmonicTrace
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TruncatedGaussianMassLaw
open ArchonPhysics.GaussianIIDMassPhaseEnsemble
open Filter MeasureTheory Module RCLike InnerProductSpace Topology
open scoped Matrix

noncomputable section

/-- The first index in the decreasing ordered spectrum. -/
def leadingOrderedModeIndex (N : Nat) [NeZero N] : OrderedModeIndex N :=
  ⟨0, by simpa [Lattice.Site] using NeZero.pos N⟩

/-- Every real Hermitian diagonal entry lies below the leading ordered
eigenvalue. -/
theorem diagonal_le_leadingOrderedEigenvalue
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : HermitianMatrix ι) (i : ι) :
    A.1 i i ≤ orderedEigenvalue A ⟨0, Fintype.card_pos⟩ := by
  let T := Matrix.toEuclideanLin (𝕜 := Real) A.1
  have hT : T.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr A.2
  let x : EuclideanSpace Real ι := EuclideanSpace.single i 1
  have hx : x ≠ 0 := by
    intro h
    have hi := congrArg (fun y : EuclideanSpace Real ι ↦ y i) h
    simp [x] at hi
  have h := rayleigh_le_largest_eigenvalue hT
    (Fintype.card ι) finrank_euclideanSpace Fintype.card_pos x hx
  have hentry :
      ((Matrix.toEuclideanLin A.1) x : EuclideanSpace Real ι) i =
        A.1 i i := by
    change (A.1 *ᵥ x.ofLp) i = A.1 i i
    simp [x, Matrix.mulVec]
  have hnorm : ‖x‖ ^ 2 = 1 := by simp [x]
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [dotProduct, star_id_of_comm] at h
  have hinner : (∑ j, x j * (T x) j) = A.1 i i := by
    simp [x, hentry, T]
  rw [hinner, hnorm, div_one] at h
  change A.1 i i ≤ A.property.eigenvalues₀
    ⟨0, Fintype.card_pos⟩ at h
  exact h

/-- A diagonal entry of the periodic mass-weighted harmonic matrix is exactly
twice the reciprocal mass. -/
theorem massWeightedHarmonicMatrix_diagonal_eq_two_mul_inv
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (m : Lattice.PositiveMassConfig N) (i : Lattice.Site N) :
    massWeightedHarmonicMatrix m i i = 2 * (m.mass i)⁻¹ := by
  rw [massWeightedHarmonicMatrix_apply]
  simp_rw [massWeightedDifferenceMatrix_apply]
  calc
    (∑ k, (differenceMatrix k i * (Real.sqrt (m.mass i))⁻¹) *
        (differenceMatrix k i * (Real.sqrt (m.mass i))⁻¹)) =
      (Real.sqrt (m.mass i))⁻¹ ^ 2 *
        ∑ k, differenceMatrix k i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = (Real.sqrt (m.mass i))⁻¹ ^ 2 * 2 := by
      rw [differenceMatrix_column_sq_sum hN i]
    _ = 2 * (m.mass i)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (m.mass_pos i).le]
      ring

/-- Frozen support `[4/5,6/5]` gives the leading squared frequency the
pointwise floor `5/3`. -/
theorem gaussian_leadingOrderedEigenvalue_ge_five_thirds
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) (sample : Omega) :
    (5 / 3 : Real) ≤
      orderedEigenvalue
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) sample))
        (leadingOrderedModeIndex N) := by
  let m := ensemble.restrictPositiveMass (N := N) sample
  let i : Lattice.Site N := 0
  have hmass : m.mass i ≤ (6 / 5 : Real) := by
    simpa [m, i, RandomEnsemble.massUpper] using
      (ensemble.mass_mem_support i.val sample).2
  have hinv : (5 / 6 : Real) ≤ (m.mass i)⁻¹ := by
    have h := (inv_le_inv₀ (by norm_num : (0 : Real) < 6 / 5)
      (m.mass_pos i)).2 hmass
    norm_num at h ⊢
    exact h
  have hdiag := diagonal_le_leadingOrderedEigenvalue
    (harmonicHermitian m) i
  change massWeightedHarmonicMatrix m i i ≤
    orderedEigenvalue (harmonicHermitian m) ⟨0, Fintype.card_pos⟩ at hdiag
  rw [massWeightedHarmonicMatrix_diagonal_eq_two_mul_inv hN] at hdiag
  have htop : (5 / 3 : Real) ≤
      orderedEigenvalue (harmonicHermitian m) ⟨0, Fintype.card_pos⟩ := by
    nlinarith
  simpa [m, leadingOrderedModeIndex] using htop

/-- Square-root form of the same deterministic leading-frequency floor. -/
theorem gaussian_leadingOrderedModeFrequency_ge_sqrt_five_thirds
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N) (sample : Omega) :
    Real.sqrt (5 / 3 : Real) ≤
      orderedModeFrequency
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) sample))
        (leadingOrderedModeIndex N) := by
  exact Real.sqrt_le_sqrt
    (gaussian_leadingOrderedEigenvalue_ge_five_thirds
      ensemble hN sample)

/-- Named finite-volume Gaussian consumer.  Almost surely the normalized
leading-mode cross remainder has the explicit `1/N` bound. -/
theorem gaussian_ae_normalized_leading_crossOrbit_le_inverseVolume
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (kappa g : Real) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (htime : 0 < time) :
    ∀ᵐ sample ∂ensemble.probability,
      let m := ensemble.restrictPositiveMass (N := N) sample
      let q := leadingOrderedModeIndex N
      |(freeQuadraticCrossSwapOrbitCoherentRemainder
          (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
          m (orderedIndexEquiv q)
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time).re| / (N : Real) ^ 2 ≤
        2 * (kappa * g) ^ 2 * energyBound ^ 2 /
          ((N : Real) * Real.sqrt (5 / 3 : Real) * time) := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN]
      with sample hsimple
  let m := ensemble.restrictPositiveMass (N := N) sample
  let q := leadingOrderedModeIndex N
  have hfloor : Real.sqrt (5 / 3 : Real) ≤
      orderedModeFrequency (harmonicHermitian m) q :=
    gaussian_leadingOrderedModeFrequency_ge_sqrt_five_thirds
      ensemble hN sample
  have hfloorPos : 0 < Real.sqrt (5 / 3 : Real) := by positivity
  have hfrequency : 0 <
      orderedModeFrequency (harmonicHermitian m) q :=
    hfloorPos.trans_le hfloor
  have hmain := normalized_abs_re_physical_crossOrbit_le_inverseVolume
    kappa g m q energy energyBound hsimple henergyBoundNonneg
    henergy henergyBound hfrequency htime
  dsimp only
  refine hmain.trans ?_
  have hnum : 0 ≤ 2 * (kappa * g) ^ 2 * energyBound ^ 2 := by positivity
  have hNreal : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply div_le_div_of_nonneg_left hnum
  · positivity
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfloor hNreal.le) htime.le

/-- Varying-volume leading-mode cross remainder, normalized by `N^2` and
started at the nondegenerate chain size `N = 2`. -/
def gaussianLeadingNormalizedCrossOrbit
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    (kappa g : Real)
    (energy : ∀ n : Nat, Lattice.Site (n + 2) → Real)
    (time : Real) (sample : Omega) (n : Nat) : Real :=
  let N := n + 2
  let m := ensemble.restrictPositiveMass (N := N) sample
  let q := leadingOrderedModeIndex N
  |(freeQuadraticCrossSwapOrbitCoherentRemainder
      (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
      m (orderedIndexEquiv q)
      (phaseEnergyRadius (energy n) (modeFrequency m)) (modeFrequency m)
      time).re| / (N : Real) ^ 2

/-- Strongest assumption-free-in-spectrum conclusion for the frozen Gaussian
ensemble: at fixed positive time and a deterministic uniform modal-energy
ceiling, the `N^2`-normalized leading-mode cross remainder tends to zero
almost surely.  Neither random phase cancellation nor independence of
spectral coefficients is invoked. -/
theorem gaussianLeadingNormalizedCrossOrbit_tendsto_zero_ae
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    (kappa g : Real)
    (energy : ∀ n : Nat, Lattice.Site (n + 2) → Real)
    (energyBound : Real)
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ n mode, 0 ≤ energy n mode)
    (henergyBound : ∀ n mode, energy n mode ≤ energyBound)
    {time : Real} (htime : 0 < time) :
    ∀ᵐ sample ∂ensemble.probability,
      Tendsto
        (gaussianLeadingNormalizedCrossOrbit
          ensemble kappa g energy time sample)
        atTop (nhds 0) := by
  have hall : ∀ᵐ sample ∂ensemble.probability, ∀ n : Nat,
      gaussianLeadingNormalizedCrossOrbit
          ensemble kappa g energy time sample n ≤
        2 * (kappa * g) ^ 2 * energyBound ^ 2 /
          (((n + 2 : Nat) : Real) * Real.sqrt (5 / 3 : Real) * time) := by
    apply MeasureTheory.ae_all_iff.mpr
    intro n
    simpa [gaussianLeadingNormalizedCrossOrbit] using
      (gaussian_ae_normalized_leading_crossOrbit_le_inverseVolume
        ensemble (N := n + 2) (by omega) kappa g (energy n)
        energyBound henergyBoundNonneg (henergy n) (henergyBound n) htime)
  filter_upwards [hall] with sample hsample
  apply squeeze_zero
  · intro n
    unfold gaussianLeadingNormalizedCrossOrbit
    positivity
  · exact hsample
  · have hshift : Tendsto
        (fun n : Nat ↦ 1 / (((n + 2 : Nat) : Real)))
        atTop (nhds (0 : Real)) := by
      simpa [Function.comp_def] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := Real)).comp
          (tendsto_add_atTop_nat 2)
    have hfloorNe : Real.sqrt (5 / 3 : Real) ≠ 0 := by positivity
    have htimeNe : time ≠ 0 := htime.ne'
    have hrhs :
        (fun n : Nat ↦
          2 * (kappa * g) ^ 2 * energyBound ^ 2 /
            (((n + 2 : Nat) : Real) * Real.sqrt (5 / 3 : Real) * time)) =
        (fun n : Nat ↦
          (2 * (kappa * g) ^ 2 * energyBound ^ 2 /
            (Real.sqrt (5 / 3 : Real) * time)) *
              (1 / (((n + 2 : Nat) : Real)))) := by
      funext n
      have hN : (((n + 2 : Nat) : Real)) ≠ 0 := by positivity
      field_simp [hN, hfloorNe, htimeNe]
    rw [hrhs]
    simpa using tendsto_const_nhds.mul hshift

end

end ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer
