import ArchonPhysics.ActualTwoMassChildRepeatedPerSiteLInfinity
import ArchonPhysics.FrozenUniformCollisionCompactSupport

/-!
# One-dimensional density bound for child-repeated mismatch

A planar `L∞` bound alone cannot be pushed through
`(omega_parent, omega_child) ↦ omega_parent - 2 omega_child`, because the
fibres are unbounded.  The physical frequency square supplies the missing
finite transverse width.  We prove the exact measurable-set estimate

`volume ({mismatch ∈ A} ∩ [0,W]²) ≤ W * volume A`

and use it to transport a planar density ceiling `C` to the scalar ceiling
`C * W`.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.ChildRepeatedMismatchPushforwardLInfinity

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteLInfinity
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ChildRepeatedCanonicalClusterLimit
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedReducedResonanceStripVolume
open ArchonPhysics.ChildRepeatedScalarClusterHybridLift
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

local instance pairVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- A measurable mismatch set has at most its one-dimensional volume times
the transverse child-frequency width inside the physical square. -/
theorem volume_childRepeatedDecayMismatch_preimage_inter_frequencySquare_le
    {A : Set Real} (hA : MeasurableSet A)
    {W : Real} :
    (volume : Measure (Real × Real))
        (childRepeatedDecayMismatch ⁻¹' A ∩
          childRepeatedFrequencySquare W) ≤
      ENNReal.ofReal W * (volume : Measure Real) A := by
  let target := childRepeatedDecayMismatch ⁻¹' A ∩
    childRepeatedFrequencySquare W
  have htarget : MeasurableSet target :=
    (measurable_childRepeatedDecayMismatch hA).inter
      (childRepeatedFrequencySquare_isClosed W).measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm htarget]
  calc
    (∫⁻ child, (volume : Measure Real)
        ((fun parent => (parent, child)) ⁻¹' target) ∂volume) ≤
      ∫⁻ child in Icc (0 : Real) W,
        (volume : Measure Real) A ∂volume := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_mono_ae
      filter_upwards with child
      by_cases hchild : child ∈ Icc (0 : Real) W
      · rw [indicator_of_mem hchild]
        calc
          (volume : Measure Real)
              ((fun parent => (parent, child)) ⁻¹' target) ≤
            (volume : Measure Real)
              ((fun parent => parent - 2 * child) ⁻¹' A) := by
                apply measure_mono
                intro parent hparent
                exact hparent.1
          _ = (volume : Measure Real) A := by
            have hpreimage :
                ((fun parent => parent - 2 * child) ⁻¹' A) =
                  ((fun parent => (-2 * child) + parent) ⁻¹' A) := by
              apply congrArg (fun f : Real → Real => f ⁻¹' A)
              funext parent
              ring
            rw [hpreimage, measure_preimage_add]
      · rw [indicator_of_notMem hchild]
        have hsection :
            ((fun parent => (parent, child)) ⁻¹' target) = ∅ := by
          ext parent
          simp only [mem_preimage, mem_empty_iff_false]
          constructor
          · intro hparent
            exact hchild hparent.2.2
          · exact False.elim
        rw [hsection, measure_empty]
    _ = (volume : Measure Real) A *
        (volume : Measure Real) (Icc (0 : Real) W) := by
      rw [setLIntegral_const]
    _ = ENNReal.ofReal W * (volume : Measure Real) A := by
      rw [Real.volume_Icc]
      simp only [sub_zero]
      ac_rfl

/-- A square-supported planar density ceiling pushes forward to a scalar
density ceiling equal to the planar ceiling times the square width. -/
theorem map_childRepeatedDecayMismatch_le_smul_volume_of_le_volume_of_support
    (measure : Measure (Real × Real))
    (C : ENNReal) {W : Real}
    (hle : measure ≤ C • (volume : Measure (Real × Real)))
    (hsupport : measure (childRepeatedFrequencySquare W)ᶜ = 0) :
    Measure.map childRepeatedDecayMismatch measure ≤
      (C * ENNReal.ofReal W) • (volume : Measure Real) := by
  have haesupport : ∀ᵐ frequency ∂measure,
      frequency ∈ childRepeatedFrequencySquare W :=
    ae_iff.mpr hsupport
  apply Measure.le_iff.2
  intro A hA
  rw [Measure.map_apply measurable_childRepeatedDecayMismatch hA,
    Measure.smul_apply, smul_eq_mul]
  calc
    measure (childRepeatedDecayMismatch ⁻¹' A) =
        measure
          (childRepeatedDecayMismatch ⁻¹' A ∩
            childRepeatedFrequencySquare W) := by
      rw [← Measure.measure_inter_eq_of_ae haesupport]
      rw [inter_comm]
    _ ≤ (C • (volume : Measure (Real × Real)))
          (childRepeatedDecayMismatch ⁻¹' A ∩
            childRepeatedFrequencySquare W) :=
      Measure.le_iff'.1 hle _
    _ = C * (volume : Measure (Real × Real))
          (childRepeatedDecayMismatch ⁻¹' A ∩
            childRepeatedFrequencySquare W) := by
      rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ C *
        (ENNReal.ofReal W * (volume : Measure Real) A) :=
      mul_le_mul_right
        (volume_childRepeatedDecayMismatch_preimage_inter_frequencySquare_le
          hA) C
    _ = (C * ENNReal.ofReal W) * (volume : Measure Real) A := by
      rw [mul_assoc]

/-- The reduced law of every child-repeated hybrid lift remains inside the
uniform physical square. -/
theorem childRepeatedScalarClusterHybridLift_reduced_compl_frequencySquare_eq_zero
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget) :
    ((((lift.markedTarget.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection :
      FiniteMeasure (Real × Real)) : Measure (Real × Real)))
        (childRepeatedFrequencySquare collisionFrequencyCeiling)ᶜ = 0 := by
  have hmarkedSupport :=
    canonicalChildRepeatedMarkedWeakLimit_compl_uniformSupport_eq_zero
      ensemble omega (fun j => size (lift.subsequence j))
      lift.markedTarget lift.markedTendsto
  rw [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_map,
    Measure.map_map measurable_childRepeatedFrequencyProjection
      measurable_forgetRankFrequencyTriple,
    Measure.map_apply
      (measurable_childRepeatedFrequencyProjection.comp
        measurable_forgetRankFrequencyTriple)
      (childRepeatedFrequencySquare_isClosed
        collisionFrequencyCeiling).measurableSet.compl]
  apply measure_mono_null _ hmarkedSupport
  intro marks hmarks
  simp only [mem_preimage, mem_compl_iff] at hmarks ⊢
  intro hsupport
  apply hmarks
  exact
    ⟨⟨(hsupport.1 0).2, (hsupport.2 0).2⟩,
      ⟨(hsupport.1 1).2, (hsupport.2 1).2⟩⟩

/-- A planar `L∞` reduced-law estimate therefore yields a scalar mismatch
`L∞` estimate with the explicit transverse-width factor `sqrt 5`. -/
theorem childRepeatedScalarClusterHybridLift_scalar_le_volume_of_reduced_le_volume
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget)
    (C : ENNReal)
    (hreduced :
      ((((lift.markedTarget.map forgetRankFrequencyTriple).map
          childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real))) ≤
        C • (volume : Measure (Real × Real))) :
    (scalarTarget : Measure Real) ≤
      (C * ENNReal.ofReal collisionFrequencyCeiling) •
        (volume : Measure Real) := by
  rw [lift.scalar_eq_mismatch, lift.mismatchReduced]
  exact map_childRepeatedDecayMismatch_le_smul_volume_of_le_volume_of_support
    (((lift.markedTarget.map forgetRankFrequencyTriple).map
      childRepeatedFrequencyProjection :
      FiniteMeasure (Real × Real)) : Measure (Real × Real))
    C hreduced
    (childRepeatedScalarClusterHybridLift_reduced_compl_frequencySquare_eq_zero
      lift)

/-- End-to-end scalar `L∞` closure from finite-volume planar estimates
with vanishing bad error. -/
theorem childRepeatedScalarClusterHybridLift_scalar_le_volume_of_reduced_vanishingError
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      ensemble omega size scalarTarget)
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ j A, MeasurableSet A →
      (((canonicalChildRepeatedFrequencyPerSiteFiniteMeasure ensemble
          (size (lift.subsequence j)) omega).map
          childRepeatedFrequencyProjection :
        FiniteMeasure (Real × Real)) : Measure (Real × Real)) A ≤
        C * (volume : Measure (Real × Real)) A + error j) :
    (scalarTarget : Measure Real) ≤
      (C * ENNReal.ofReal collisionFrequencyCeiling) •
        (volume : Measure Real) := by
  apply childRepeatedScalarClusterHybridLift_scalar_le_volume_of_reduced_le_volume
    lift C
  exact
    childRepeatedScalarClusterHybridLift_reduced_le_volume_of_vanishingError
      lift C hC error herror hbound

end

end ArchonPhysics.ChildRepeatedMismatchPushforwardLInfinity
