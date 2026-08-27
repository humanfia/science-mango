import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import ArchonPhysics.ActualTwoMassChildRepeatedAnnealedLInfinity
import ArchonPhysics.ActualTwoMassChildRepeatedDeterministicBridge
import ArchonPhysics.CanonicalChildRepeatedAnnealedAtlasSmallBall
import ArchonPhysics.ChildRepeatedAnnealedWeakTestLInfinity
import ArchonPhysics.CanonicalOnShellFrequencyMarginalBridge

/-!
# Genuine frequency--mismatch joint coordinates for the child-repeated sector

For a child-repeated decay triple the two independent frequencies are
`(omega_parent, omega_child)` and the mismatch is
`omega_parent - 2 * omega_child`.  Retaining the parent frequency gives a
linear change of variables of determinant `-2`; retaining either repeated
child frequency gives one of determinant `-1`.  Thus the exact Lebesgue
pushforward constants are respectively `1 / 2` and `1`.

This module proves those change-of-variables identities and connects them to
the actual two-mass and canonical child-repeated measures.  It then supplies
the joint hypothesis consumed by `FrequencyMismatchKernelMarginalDomination`.
No realization-wise density bound for an atomic finite-volume measure is
asserted.
-/

open scoped ENNReal Topology

namespace ArchonPhysics.ChildRepeatedFrequencyMismatchJointDomination

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedAnnealedLInfinity
open ArchonPhysics.ActualTwoMassChildRepeatedDeterministicBridge
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalChildRepeatedAnnealedAtlasSmallBall
open ArchonPhysics.CanonicalOnShellFrequencyMarginalBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.ChildRepeatedAnnealedWeakTestLInfinity
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedFrequencyDiagonalWeakLimit
open ArchonPhysics.ChildRepeatedScalarClusterHybridLift
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.FrequencyMismatchKernelMarginalDomination
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassPositiveCollisionData
open Filter MeasureTheory Set

noncomputable section

/-! ## Exact linear coordinates -/

/-- The frequency carried by `leg` after the child-frequency diagonal has
been parametrized by `(omega_parent, omega_child)`. -/
def childRepeatedLegFrequency (leg : Fin 3)
    (frequency : Real × Real) : Real :=
  (childRepeatedFrequencyDiagonalLift frequency) leg

theorem continuous_childRepeatedLegFrequency (leg : Fin 3) :
    Continuous (childRepeatedLegFrequency leg) := by
  unfold childRepeatedLegFrequency
  exact continuous_apply leg |>.comp
    continuous_childRepeatedFrequencyDiagonalLift

theorem measurable_childRepeatedLegFrequency (leg : Fin 3) :
    Measurable (childRepeatedLegFrequency leg) :=
  (continuous_childRepeatedLegFrequency leg).measurable

/-- Parent-leg coordinates
`(parent, child) -> (parent, parent - 2 * child)`. -/
def childRepeatedParentFrequencyMismatchLinearEquiv :
    (Real × Real) ≃ₗ[Real] (Real × Real) where
  toFun frequency := (frequency.1, frequency.1 - 2 * frequency.2)
  invFun joint := (joint.1, (joint.1 - joint.2) / 2)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  left_inv x := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  right_inv x := by
    apply Prod.ext
    · rfl
    · dsimp
      ring

/-- Child-leg coordinates
`(parent, child) -> (child, parent - 2 * child)`. -/
def childRepeatedChildFrequencyMismatchLinearEquiv :
    (Real × Real) ≃ₗ[Real] (Real × Real) where
  toFun frequency := (frequency.2, frequency.1 - 2 * frequency.2)
  invFun joint := (joint.2 + 2 * joint.1, joint.1)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  left_inv x := by
    apply Prod.ext
    · dsimp
      ring
    · rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · dsimp
      ring

/-- The genuine invertible `(leg frequency, mismatch)` map for every one of
the three legs.  The two repeated child legs use the same equivalence. -/
def childRepeatedLegFrequencyMismatchLinearEquiv (leg : Fin 3) :
    (Real × Real) ≃ₗ[Real] (Real × Real) :=
  if leg = 0 then childRepeatedParentFrequencyMismatchLinearEquiv
  else childRepeatedChildFrequencyMismatchLinearEquiv

/-- Exact inverse-Jacobian factor for the leg coordinate map. -/
def childRepeatedLegLebesgueConstant (leg : Fin 3) : ENNReal :=
  if leg = 0 then (2 : ENNReal)⁻¹ else 1

@[simp] theorem childRepeatedLegFrequency_zero (frequency : Real × Real) :
    childRepeatedLegFrequency 0 frequency = frequency.1 := by
  rfl

@[simp] theorem childRepeatedLegFrequency_one (frequency : Real × Real) :
    childRepeatedLegFrequency 1 frequency = frequency.2 := by
  rfl

@[simp] theorem childRepeatedLegFrequency_two (frequency : Real × Real) :
    childRepeatedLegFrequency 2 frequency = frequency.2 := by
  rfl

theorem childRepeatedLegFrequencyMismatchLinearEquiv_apply
    (leg : Fin 3) (frequency : Real × Real) :
    childRepeatedLegFrequencyMismatchLinearEquiv leg frequency =
      frequencyMismatchCoordinates (childRepeatedLegFrequency leg)
        childRepeatedDecayMismatch frequency := by
  fin_cases leg <;>
    simp [childRepeatedLegFrequencyMismatchLinearEquiv,
      childRepeatedParentFrequencyMismatchLinearEquiv,
      childRepeatedChildFrequencyMismatchLinearEquiv,
      frequencyMismatchCoordinates, childRepeatedDecayMismatch]

theorem continuous_childRepeatedLegFrequencyMismatchLinearEquiv
    (leg : Fin 3) :
    Continuous (childRepeatedLegFrequencyMismatchLinearEquiv leg) :=
  (childRepeatedLegFrequencyMismatchLinearEquiv leg).toLinearMap
    |>.continuous_of_finiteDimensional

theorem measurable_childRepeatedLegFrequencyMismatchLinearEquiv
    (leg : Fin 3) :
    Measurable (childRepeatedLegFrequencyMismatchLinearEquiv leg) :=
  (continuous_childRepeatedLegFrequencyMismatchLinearEquiv leg).measurable

theorem toMatrix_childRepeatedParentFrequencyMismatchLinearEquiv :
    LinearMap.toMatrix (Module.Basis.finTwoProd Real)
      (Module.Basis.finTwoProd Real)
      (childRepeatedParentFrequencyMismatchLinearEquiv :
        (Real × Real) →ₗ[Real] (Real × Real)) =
      !![(1 : Real), 0; 1, -2] := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [childRepeatedParentFrequencyMismatchLinearEquiv]

theorem det_childRepeatedParentFrequencyMismatchLinearEquiv :
    LinearMap.det (childRepeatedParentFrequencyMismatchLinearEquiv :
      (Real × Real) →ₗ[Real] (Real × Real)) = -2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd Real)
    (childRepeatedParentFrequencyMismatchLinearEquiv :
      (Real × Real) →ₗ[Real] (Real × Real))]
  rw [toMatrix_childRepeatedParentFrequencyMismatchLinearEquiv]
  norm_num [Matrix.det_fin_two]

theorem toMatrix_childRepeatedChildFrequencyMismatchLinearEquiv :
    LinearMap.toMatrix (Module.Basis.finTwoProd Real)
      (Module.Basis.finTwoProd Real)
      (childRepeatedChildFrequencyMismatchLinearEquiv :
        (Real × Real) →ₗ[Real] (Real × Real)) =
      !![(0 : Real), 1; 1, -2] := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [childRepeatedChildFrequencyMismatchLinearEquiv]

theorem det_childRepeatedChildFrequencyMismatchLinearEquiv :
    LinearMap.det (childRepeatedChildFrequencyMismatchLinearEquiv :
      (Real × Real) →ₗ[Real] (Real × Real)) = -1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd Real)
    (childRepeatedChildFrequencyMismatchLinearEquiv :
      (Real × Real) →ₗ[Real] (Real × Real))]
  rw [toMatrix_childRepeatedChildFrequencyMismatchLinearEquiv]
  norm_num [Matrix.det_fin_two]

local instance pairVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Exact half-density change of variables for the parent leg. -/
theorem map_childRepeatedParentFrequencyMismatchLinearEquiv_volume :
    Measure.map
        (childRepeatedParentFrequencyMismatchLinearEquiv :
          (Real × Real) → (Real × Real))
        ((volume : Measure Real).prod (volume : Measure Real)) =
      (2 : ENNReal)⁻¹ •
        ((volume : Measure Real).prod (volume : Measure Real)) := by
  rw [← Measure.volume_eq_prod]
  change Measure.map
      (childRepeatedParentFrequencyMismatchLinearEquiv :
        (Real × Real) →ₗ[Real] (Real × Real)) volume = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Real × Real)) (by
      rw [det_childRepeatedParentFrequencyMismatchLinearEquiv]
      norm_num)]
  rw [det_childRepeatedParentFrequencyMismatchLinearEquiv]
  congr 1
  rw [show |(-2 : Real)⁻¹| = (2 : Real)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- Exact unit-density change of variables for either child leg. -/
theorem map_childRepeatedChildFrequencyMismatchLinearEquiv_volume :
    Measure.map
        (childRepeatedChildFrequencyMismatchLinearEquiv :
          (Real × Real) → (Real × Real))
        ((volume : Measure Real).prod (volume : Measure Real)) =
      ((volume : Measure Real).prod (volume : Measure Real)) := by
  rw [← Measure.volume_eq_prod]
  change Measure.map
      (childRepeatedChildFrequencyMismatchLinearEquiv :
        (Real × Real) →ₗ[Real] (Real × Real)) volume = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Real × Real)) (by
      rw [det_childRepeatedChildFrequencyMismatchLinearEquiv]
      norm_num)]
  rw [det_childRepeatedChildFrequencyMismatchLinearEquiv]
  norm_num

/-- Exact Lebesgue pushforward formula, uniformly indexed by all three legs. -/
theorem map_childRepeatedLegFrequencyMismatchLinearEquiv_volume
    (leg : Fin 3) :
    Measure.map
        (childRepeatedLegFrequencyMismatchLinearEquiv leg :
          (Real × Real) → (Real × Real))
        ((volume : Measure Real).prod (volume : Measure Real)) =
      childRepeatedLegLebesgueConstant leg •
        ((volume : Measure Real).prod (volume : Measure Real)) := by
  fin_cases leg
  · exact map_childRepeatedParentFrequencyMismatchLinearEquiv_volume
  · simpa [childRepeatedLegFrequencyMismatchLinearEquiv,
      childRepeatedLegLebesgueConstant] using
      map_childRepeatedChildFrequencyMismatchLinearEquiv_volume
  · simpa [childRepeatedLegFrequencyMismatchLinearEquiv,
      childRepeatedLegLebesgueConstant] using
      map_childRepeatedChildFrequencyMismatchLinearEquiv_volume

/-! ## Transport of domination and absolute continuity -/

/-- A planar density bound transports with the exact inverse-Jacobian
constant: `C / 2` for the parent and `C` for either child. -/
theorem map_childRepeatedLegFrequencyMismatchLinearEquiv_le_volume
    (measure : Measure (Real × Real)) (leg : Fin 3) (C : ENNReal)
    (hle : measure ≤
      C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg) measure ≤
      (C * childRepeatedLegLebesgueConstant leg) •
        ((volume : Measure Real).prod (volume : Measure Real)) := by
  calc
    Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg) measure ≤
        Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg)
          (C • ((volume : Measure Real).prod (volume : Measure Real))) :=
      Measure.map_mono hle
        (measurable_childRepeatedLegFrequencyMismatchLinearEquiv leg)
    _ = C • Measure.map
        (childRepeatedLegFrequencyMismatchLinearEquiv leg)
          ((volume : Measure Real).prod (volume : Measure Real)) := by
      rw [Measure.map_smul]
    _ = C • (childRepeatedLegLebesgueConstant leg •
        ((volume : Measure Real).prod (volume : Measure Real))) := by
      rw [map_childRepeatedLegFrequencyMismatchLinearEquiv_volume]
    _ = (C * childRepeatedLegLebesgueConstant leg) •
        ((volume : Measure Real).prod (volume : Measure Real)) := by
      rw [mul_smul]

/-- Invertibility also transports planar absolute continuity for every leg. -/
theorem map_childRepeatedLegFrequencyMismatchLinearEquiv_absolutelyContinuous
    (measure : Measure (Real × Real)) (leg : Fin 3)
    (hac : measure ≪
      ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg) measure ≪
      ((volume : Measure Real).prod (volume : Measure Real)) := by
  have hmap :=
    hac.map (measurable_childRepeatedLegFrequencyMismatchLinearEquiv leg)
  rw [map_childRepeatedLegFrequencyMismatchLinearEquiv_volume] at hmap
  exact hmap.trans Measure.smul_absolutelyContinuous

/-- The abstract kernel's joint coordinates are definitionally the genuine
leg linear equivalence on the reduced child plane. -/
theorem frequencyMismatchCoordinates_childRepeated_eq_linearEquiv
    (leg : Fin 3) :
    frequencyMismatchCoordinates (childRepeatedLegFrequency leg)
        childRepeatedDecayMismatch =
      childRepeatedLegFrequencyMismatchLinearEquiv leg := by
  funext frequency
  exact
    (childRepeatedLegFrequencyMismatchLinearEquiv_apply leg frequency).symm

/-- A reduced planar bound is exactly the raw joint bound required by the
unit-mass mismatch-kernel theorem. -/
theorem map_childRepeatedFrequencyMismatchCoordinates_le_volume
    (measure : Measure (Real × Real)) (leg : Fin 3) (C : ENNReal)
    (hle : measure ≤
      C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map
        (frequencyMismatchCoordinates (childRepeatedLegFrequency leg)
          childRepeatedDecayMismatch) measure ≤
      (C * childRepeatedLegLebesgueConstant leg) •
        ((volume : Measure Real).prod (volume : Measure Real)) := by
  rw [frequencyMismatchCoordinates_childRepeated_eq_linearEquiv]
  exact map_childRepeatedLegFrequencyMismatchLinearEquiv_le_volume
    measure leg C hle

/-- The normalized finite-time resonance kernel therefore gives a genuinely
time-uniform one-leg density bound with constant `C / 2` or `C`. -/
theorem map_childRepeatedLegFrequency_broadenedResonanceMeasure_le_volume
    (measure : FiniteMeasure (Real × Real))
    {T : Real} (hT : 0 < T) (leg : Fin 3) (C : ENNReal)
    (hle : (measure : Measure (Real × Real)) ≤
      C • ((volume : Measure Real).prod (volume : Measure Real))) :
    Measure.map (childRepeatedLegFrequency leg)
        (broadenedResonanceMeasure measure childRepeatedDecayMismatch
          measurable_childRepeatedDecayMismatch T hT :
            Measure (Real × Real)) ≤
      (C * childRepeatedLegLebesgueConstant leg) •
        (volume : Measure Real) := by
  exact
    map_frequency_broadenedResonanceMeasure_le_volume_of_joint_le
      measure measurable_childRepeatedDecayMismatch hT
      (childRepeatedLegFrequency leg)
      (measurable_childRepeatedLegFrequency leg)
      (C * childRepeatedLegLebesgueConstant leg)
      (map_childRepeatedFrequencyMismatchCoordinates_le_volume
        (measure : Measure (Real × Real)) leg C hle)

end

end ArchonPhysics.ChildRepeatedFrequencyMismatchJointDomination
