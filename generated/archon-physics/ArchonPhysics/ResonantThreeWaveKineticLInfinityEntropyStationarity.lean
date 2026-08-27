import ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity

/-!
# Zero entropy production implies L-infinity stationarity

For a canonical `L-infinity` class with a strict essential floor, the
floor-preserving representative is pointwise positive.  Equality in the
continuum H-theorem therefore kills its triad flux almost everywhere, hence
the signed collision measure, its Radon--Nikodym collision vector, and finally
the genuine quotient collision map all vanish.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticLInfinityEntropyStationarity

open Filter MeasureTheory
open ArchonPhysics.BoundedMeasurableAEFrequencyBalanceRigidity
open ArchonPhysics.ResonantThreeWaveKineticEntropy
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open ArchonPhysics.ResonantThreeWaveKineticLInfinityRigidity
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ThreeWaveCollisionAlgebra
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Zero entropy production annihilates the triad flux of any bounded
measurable action with a strict pointwise floor. -/
theorem triadFlux_ae_eq_zero_of_entropyProduction_eq_zero
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode → Real} (haction : IsBoundedMeasurable action)
    (floor : Real) (hfloor : 0 < floor)
    (hactionFloor : ∀ mode, floor ≤ action mode)
    (hzero : continuumLogEntropyProduction collision action = 0) :
    triadFlux action =ᵐ[
      (collision.collisionMeasure : Measure (Fin 3 → Mode))] 0 := by
  have hmismatch :=
    (continuumLogEntropyProduction_eq_zero_iff_inverseActionMismatch_ae
      collision haction floor hfloor hactionFloor).mp hzero
  filter_upwards [hmismatch] with triad htriad
  have hpositive (leg : Fin 3) : 0 < action (triad leg) :=
    hfloor.trans_le (hactionFloor (triad leg))
  have hflux :=
    (collisionFlux_eq_zero_iff_inverseActionMismatch_eq_zero
      (hpositive 0) (hpositive 1) (hpositive 2)).mpr htriad
  simpa only [triadFlux, Pi.zero_apply] using hflux

/-- The pointwise RN collision vector vanishes almost everywhere whenever
the positive action has zero entropy production. -/
theorem collisionVector_ae_eq_zero_of_entropyProduction_eq_zero
    (collision : ResonantThreeWaveMeasure Mode)
    {action : Mode → Real} (haction : IsBoundedMeasurable action)
    (floor : Real) (hfloor : 0 < floor)
    (hactionFloor : ∀ mode, floor ≤ action mode)
    (hzero : continuumLogEntropyProduction collision action = 0) :
    collisionVector collision action =ᵐ[
      collisionReferenceMeasure collision] 0 := by
  have hflux := triadFlux_ae_eq_zero_of_entropyProduction_eq_zero
    collision haction floor hfloor hactionFloor hzero
  have hfluxMeasure : fluxSignedTriadMeasure collision action = 0 := by
    unfold fluxSignedTriadMeasure
    calc
      (collision.collisionMeasure : Measure (Fin 3 → Mode)).withDensityᵥ
          (triadFlux action) =
          (collision.collisionMeasure : Measure (Fin 3 → Mode)).withDensityᵥ
            (0 : (Fin 3 → Mode) → Real) :=
        WithDensityᵥEq.congr_ae hflux
      _ = 0 := withDensityᵥ_zero
  have hsigned : signedCollisionMeasure collision action = 0 := by
    unfold signedCollisionMeasure legFluxSignedMeasure
    rw [hfluxMeasure]
    simp
  have hdensity :
      (collisionReferenceMeasure collision).withDensityᵥ
          (collisionVector collision action) =
        (collisionReferenceMeasure collision).withDensityᵥ
          (0 : Mode → Real) := by
    rw [withDensity_collisionVector_eq_signedCollisionMeasure, hsigned]
    exact withDensityᵥ_zero.symm
  simpa only [Filter.EventuallyEq, Pi.zero_apply] using
    (integrable_collisionVector collision action).ae_eq_of_withDensityᵥ_eq
      (integrable_zero Mode Real (collisionReferenceMeasure collision))
      hdensity

/-- Equality in the quotient-level H-theorem makes the genuine unclipped
canonical `L-infinity` collision map vanish. -/
theorem collisionMap_eq_zero_of_canonicalEntropy_eq_zero
    (collision : ResonantThreeWaveMeasure Mode)
    {floor : Real} (hfloor : 0 < floor)
    (action : CanonicalLInfinity collision)
    (hactionFloor : AELowerBound collision floor action)
    (hzero : canonicalLogEntropyProduction collision floor action = 0) :
    collisionMap collision action = 0 := by
  let representative := positiveFloorRepresentative collision floor action
  let radius := max floor ‖action‖
  have hbounded : IsBoundedMeasurable representative :=
    positiveFloorRepresentative_isBoundedMeasurable
      collision hfloor.le action
  have hrepBound : ∀ mode, ‖representative mode‖ ≤ radius :=
    norm_positiveFloorRepresentative_le collision hfloor.le action
  have hrepAE : representative =ᵐ[
      collisionReferenceMeasure collision] action :=
    positiveFloorRepresentative_ae_eq collision action hactionFloor
  have hvectorZero : collisionVector collision representative =ᵐ[
      collisionReferenceMeasure collision] 0 :=
    collisionVector_ae_eq_zero_of_entropyProduction_eq_zero collision
      hbounded floor hfloor
      (floor_le_positiveFloorRepresentative collision floor action) hzero
  rw [collisionMap_eq_toLp_of_ae_eq collision action
    hbounded.measurable hrepBound hrepAE]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp
      (collisionVector_memLp_top_of_bound collision
        hbounded.measurable hrepBound), hvectorZero,
    Lp.coeFn_zero Real ∞ (collisionReferenceMeasure collision)]
    with mode hcoe hzeroVector hzeroClass
  rw [hcoe, hzeroVector, hzeroClass]

/-- Complete equality-case certificate: a zero-entropy positive quotient
state is stationary, and under bounded measurable balance rigidity its
inverse is frequency-proportional almost everywhere. -/
theorem stationary_and_inverseAction_ae_proportional_of_canonicalEntropy_eq_zero
    (collision : ResonantThreeWaveMeasure Mode)
    (hrigid : BoundedMeasurableAEFrequencyBalanceRigid collision)
    {floor : Real} (hfloor : 0 < floor)
    (action : CanonicalLInfinity collision)
    (hactionFloor : AELowerBound collision floor action)
    (hzero : canonicalLogEntropyProduction collision floor action = 0) :
    collisionMap collision action = 0 ∧
      ∃ scale : Real,
        ∀ᵐ mode ∂collisionReferenceMeasure collision,
          (action mode)⁻¹ = scale * collision.frequency mode := by
  exact ⟨collisionMap_eq_zero_of_canonicalEntropy_eq_zero
      collision hfloor action hactionFloor hzero,
    inverseAction_ae_proportional_of_canonicalEntropy_eq_zero
      collision hrigid hfloor action hactionFloor hzero⟩

end

end ArchonPhysics.ResonantThreeWaveKineticLInfinityEntropyStationarity
