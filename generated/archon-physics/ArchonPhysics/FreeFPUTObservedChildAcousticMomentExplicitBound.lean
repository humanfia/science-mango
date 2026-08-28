import ArchonPhysics.ExplicitRandomMassAcousticGap
import ArchonPhysics.FreeFPUTQLevelOffResonantVolumeBound

/-!
# Explicit finite-volume bound for the observed-child acoustic moment

The q-level off-resonant closure leaves the honest inverse-frequency moment

`sum_k d(observed, observed, k)^2 / omega_k`.

This file supplies a completely deterministic finite-volume envelope for that
moment.  The input is the explicit mass-weighted Poincare estimate already
proved for the physical periodic chain.  It gives a coarse positive-mode
frequency floor of order `N^(-3/2)`; fixed-common Parseval then bounds the
whole inverse moment by the reciprocal floor.  The estimate is not claimed to
be thermodynamically uniform, but it removes every hidden finite-volume gap
assumption from the second-order correction bound.
-/

namespace ArchonPhysics.FreeFPUTObservedChildAcousticMomentExplicitBound

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.ExplicitRandomMassAcousticGap
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTQLevelOffResonantVolumeBound
open ArchonPhysics.HarmonicModes
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassHarmonicTransferMatrix
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RepeatedModeTupleInteractionBound
open ArchonPhysics.RepeatedParentChildAcousticCumulativeBound
open scoped BigOperators

noncomputable section

/-- A positive physical normal mode inherits the explicit generalized-mode
eigenvalue floor. -/
theorem modeFrequencySq_ge_explicit_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper : Real) (hmUpper : 0 < mUpper)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (mode : Lattice.Site N) (hmodeFrequency : 0 < modeFrequency m mode) :
    (4 * mUpper * (N : Real) ^ 3)⁻¹ ≤ modeFrequencySq m mode := by
  let v : Lattice.Configuration N := ⇑(normalModeBasis m mode)
  let q : Lattice.Configuration N := Lattice.inverseSqrtMassAction m v
  have hvne : v ≠ 0 := by
    intro hv
    have hv' : (normalModeBasis m mode :
        EuclideanSpace Real (Lattice.Site N)) = 0 := by
      ext i
      exact congrFun hv i
    have hnorm := congrArg norm hv'
    simp at hnorm
  have hqne : q ≠ 0 := by
    intro hq
    apply hvne
    funext i
    have hi := congrFun hq i
    simp only [q, v, Lattice.inverseSqrtMassAction] at hi
    have hsqrt : Real.sqrt (m.mass i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (m.mass_pos i))
    exact (mul_eq_zero.mp hi).resolve_left (inv_ne_zero hsqrt)
  have hgeneralized : IsGeneralizedHarmonicEigenmode m
      (modeFrequencySq m mode) q := by
    exact massWeightedEigenvector_to_generalizedEigenmode m
      (modeFrequencySq m mode) v (normalMode_eigenvector m mode)
  have hlambda : 0 < modeFrequencySq m mode := by
    rw [← modeFrequency_sq]
    exact sq_pos_of_pos hmodeFrequency
  exact generalizedPositiveMode_lowerBound m mUpper hmUpper hmassUpper
    (modeFrequencySq m mode) q hgeneralized hlambda hqne

/-- Reciprocal-frequency form of the explicit finite-volume acoustic floor. -/
theorem inv_modeFrequency_le_explicit_sqrt
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper : Real) (hmUpper : 0 < mUpper)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (mode : Lattice.Site N) (hmodeFrequency : 0 < modeFrequency m mode) :
    (modeFrequency m mode)⁻¹ ≤
      Real.sqrt (4 * mUpper * (N : Real) ^ 3) := by
  let C : Real := 4 * mUpper * (N : Real) ^ 3
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hC : 0 < C := by positivity
  have hlower := modeFrequencySq_ge_explicit_of_pos
    m mUpper hmUpper hmassUpper mode hmodeFrequency
  have hone : 1 ≤ C * modeFrequency m mode ^ 2 := by
    calc
      1 = C * C⁻¹ := (mul_inv_cancel₀ hC.ne').symm
      _ ≤ C * modeFrequencySq m mode :=
        mul_le_mul_of_nonneg_left (by simpa [C] using hlower) hC.le
      _ = C * modeFrequency m mode ^ 2 := by rw [modeFrequency_sq]
  have hsqrtC : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
  have hsqrtCsq : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC.le
  have hproduct : 1 ≤ Real.sqrt C * modeFrequency m mode := by
    have hproductNonneg :
        0 ≤ Real.sqrt C * modeFrequency m mode :=
      mul_nonneg hsqrtC (modeFrequency_nonneg m mode)
    nlinarith [sq_nonneg (Real.sqrt C * modeFrequency m mode - 1)]
  rw [inv_eq_one_div, div_le_iff₀ hmodeFrequency]
  simpa [C] using hproduct

/-- The complete observed-child inverse-frequency moment is bounded by the
coarse reciprocal acoustic floor, with no simplicity or probabilistic input. -/
theorem observedChildAcousticInverseMoment_le_explicit_sqrt
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper : Real) (hmUpper : 0 < mUpper)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (observed : Lattice.Site N) :
    observedChildAcousticInverseMoment m observed ≤
      Real.sqrt (4 * mUpper * (N : Real) ^ 3) := by
  classical
  let common : OrderedModeIndex N := orderedIndexEquiv.symm observed
  let C : Real := Real.sqrt (4 * mUpper * (N : Real) ^ 3)
  let f : Lattice.Site N → Real := fun mode ↦
    repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
        common (orderedIndexEquiv.symm mode) ^ 2
  have hterm (mode : Lattice.Site N) :
      f mode / modeFrequency m mode ≤ C * f mode := by
    have hf : 0 ≤ f mode := sq_nonneg _
    by_cases hzero : modeFrequency m mode = 0
    · rw [hzero]
      simp only [div_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) hf
    · have hpos : 0 < modeFrequency m mode :=
        lt_of_le_of_ne (modeFrequency_nonneg m mode) (Ne.symm hzero)
      have hinv := inv_modeFrequency_le_explicit_sqrt
        m mUpper hmUpper hmassUpper mode hpos
      rw [div_eq_mul_inv]
      have hinvC : (modeFrequency m mode)⁻¹ ≤ C := by
        simpa only [C] using hinv
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left hinvC hf)
  rw [← sum_site_repeatedCoefficient_sq_div_frequency_eq_acousticMoment]
  change (∑ mode : Lattice.Site N, f mode / modeFrequency m mode) ≤ C
  calc
    (∑ mode : Lattice.Site N, f mode / modeFrequency m mode) ≤
        ∑ mode : Lattice.Site N, C * f mode :=
      Finset.sum_le_sum fun mode _ ↦ hterm mode
    _ = C * ∑ mode : Lattice.Site N, f mode := by
      rw [Finset.mul_sum]
    _ ≤ C * 1 := by
      apply mul_le_mul_of_nonneg_left
      · calc
          (∑ mode : Lattice.Site N, f mode) =
              ∑ other : OrderedModeIndex N,
                repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
                  common other ^ 2 := by
            apply Fintype.sum_equiv orderedIndexEquiv.symm
            intro other
            simp [f]
          _ = inverseParticipationRatio
              (harmonicNormalizedEdgeFrame m) common := by
            exact sum_harmonicRepeatedCubicCoefficient_sq_eq_ipr m common
          _ ≤ 1 := inverseParticipationRatio_le_one
            (harmonicNormalizedEdgeFrame m)
            (harmonicNormalizedEdgeFrame_orthonormal_unconditional m) common
      · exact Real.sqrt_nonneg _
    _ = C := mul_one _

/-- Substitution of the explicit acoustic floor into the complete q-level
off-resonant static mass.  Every term is now an explicit finite-volume
quantity; no minimum-frequency premise remains. -/
theorem qLevelOffResonantCorrectionStaticMass_le_explicit_acoustic_floor
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound ceiling mUpper : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved : 0 < modeFrequency m observed)
    (hCeiling : 0 ≤ ceiling)
    (hFrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling)
    (hmUpper : 0 < mUpper)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper) :
    qLevelOffResonantCorrectionStaticMass m kappa energy observed ≤
      16 * kappa ^ 2 * energyBound ^ 2 *
          Real.sqrt (4 * mUpper * (N : Real) ^ 3) +
        12 * (kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed ^ 2) * ceiling +
        8 * kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed := by
  have hbase :=
    qLevelOffResonantCorrectionStaticMass_le_acousticMoment_add_uniform
      m kappa energy observed energyBound ceiling hsimple
      hEnergyBoundNonneg hEnergy hEnergyBound hObserved hCeiling hFrequency
  have hmoment := observedChildAcousticInverseMoment_le_explicit_sqrt
    m mUpper hmUpper hmassUpper observed
  exact hbase.trans (by gcongr)

/-- Inverse-time form of the fully explicit finite-volume correction bound. -/
theorem abs_qLevelOffResonantCorrectionSum_le_explicit_acoustic_floor_over_time
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound ceiling mUpper : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved : 0 < modeFrequency m observed)
    (hCeiling : 0 ≤ ceiling)
    (hFrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling)
    (hmUpper : 0 < mUpper)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    {time : Real} (hTime : 0 < time) :
    |qLevelOffResonantCorrectionSum m kappa time energy observed| ≤
      (16 * kappa ^ 2 * energyBound ^ 2 *
          Real.sqrt (4 * mUpper * (N : Real) ^ 3) +
        12 * (kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed ^ 2) * ceiling +
        8 * kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed) / time := by
  have hbase := abs_qLevelOffResonantCorrectionSum_le_inverseTime
    m kappa energy observed hTime hObserved
  exact hbase.trans (div_le_div_of_nonneg_right
    (qLevelOffResonantCorrectionStaticMass_le_explicit_acoustic_floor
      m kappa energy observed energyBound ceiling mUpper hsimple
      hEnergyBoundNonneg hEnergy hEnergyBound hObserved hCeiling hFrequency
      hmUpper hmassUpper) hTime.le)

end

end ArchonPhysics.FreeFPUTObservedChildAcousticMomentExplicitBound
