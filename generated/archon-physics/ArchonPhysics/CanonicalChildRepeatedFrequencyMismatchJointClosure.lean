import ArchonPhysics.BoundedMassCompactSupportedFiniteMeasureSubsequence
import ArchonPhysics.ChildRepeatedAnnealedWeakTestLInfinity
import ArchonPhysics.ChildRepeatedFrequencyMismatchJointAdapter
import ArchonPhysics.ChildRepeatedInverseSensitivitySelfAveraging

/-!
# Canonical closure of the child-repeated frequency--mismatch joint bounds

The strong actual two-mass atlas sequence controls every measurable subset
of the reduced parent/child frequency plane by

`C * volume + error_n`,

with a volume-uniform finite `C` and a vanishing bad error.  This module
records that planar estimate, passes it to genuine canonical annealed weak
limits, and instantiates the exact parent `C / 2` and child `C` joint and
finite-time broadened bounds.

For a quenched marked hybrid lift, the same conclusion follows through the
existing annealed weak-test closure.  Its all-test self-averaging premise is
left verbatim: no new certificate field hides that remaining model input.
-/

open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace ArchonPhysics.CanonicalChildRepeatedFrequencyMismatchJointClosure

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedAnnealedLInfinity
open ArchonPhysics.BoundedMassCompactSupportedFiniteMeasureSubsequence
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalChildRepeatedAnnealedAtlasSmallBall
open ArchonPhysics.CanonicalOnShellFrequencyMarginalBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.ChildRepeatedAnnealedWeakTestLInfinity
open ArchonPhysics.ChildRepeatedBoundedDifferenceAudit
open ArchonPhysics.ChildRepeatedCanonicalClusterLimit
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedFrequencyMismatchJointAdapter
open ArchonPhysics.ChildRepeatedFrequencyMismatchJointDomination
open ArchonPhysics.ChildRepeatedInverseSensitivitySelfAveraging
open ArchonPhysics.ChildRepeatedMismatchPushforwardLInfinity
open ArchonPhysics.FiniteProductBoundedDifferences
open ArchonPhysics.ChildRepeatedReducedResonanceStripVolume
open ArchonPhysics.ChildRepeatedScalarClusterHybridLift
open ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Set Topology

noncomputable section

/-! ## Arbitrary-set actual-atlas estimate -/

/-- The strong actual two-mass atlas sequence gives the full planar estimate,
not merely its resonance-strip specialization. -/
theorem canonicalChildRepeatedReducedAnnealed_apply_le_of_actualAtlas
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (n : Nat) {A : Set (Real × Real)} (hA : MeasurableSet A) :
    (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure (n + 1) :
      Measure (Real × Real)) A ≤
      data.regularCeiling * (volume : Measure (Real × Real)) A +
        data.badError n := by
  calc
    (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure (n + 1) :
        Measure (Real × Real)) A ≤
      (data.atlas n).regularCeiling *
          (volume : Measure (Real × Real)) A +
        (data.atlas n).badCeiling :=
      canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply_le_of_frozenAtlas
        (n + 1) (data.site₁ n) (data.site₂ n) (data.site_ne n)
        (data.atlas n) hA
    _ ≤ data.regularCeiling * (volume : Measure (Real × Real)) A +
          data.badError n := by
      apply add_le_add _ (data.bad_le n)
      gcongr
      exact data.regular_le n

/-! ## Forced vanishing of the all-equal diagonal -/

/-- The parent/child frequency diagonal is planar Lebesgue-null. -/
theorem volume_childRepeatedParentChildDiagonal_eq_zero :
    (volume : Measure (Real × Real)) (Set.diagonal Real) = 0 := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply measurableSet_diagonal]
  simp [Set.diagonal]

/-- Any full planar actual-atlas estimate forces the entire reduced diagonal
into the exceptional budget.  In the almost-sure simple-spectrum regime this
diagonal is precisely where the all-three-modes-equal part of
`ChildRepeated` lives. -/
theorem canonicalChildRepeatedReducedAnnealed_diagonal_le_badError_of_actualAtlas
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (n : Nat) :
    (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure (n + 1) :
      Measure (Real × Real)) (Set.diagonal Real) ≤ data.badError n := by
  simpa only [volume_childRepeatedParentChildDiagonal_eq_zero, mul_zero,
    zero_add] using
      (canonicalChildRepeatedReducedAnnealed_apply_le_of_actualAtlas
        data n measurableSet_diagonal)

/-- Consequently, constructing the requested atlas sequence necessarily
proves that the normalized all-equal diagonal contribution vanishes with
volume; this obligation cannot be supplied by the regular coarea charts. -/
theorem canonicalChildRepeatedReducedAnnealed_diagonal_tendsto_zero_of_actualAtlas
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence) :
    Tendsto
      (fun n ↦
        (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure (n + 1) :
          Measure (Real × Real)) (Set.diagonal Real))
      atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (f := fun n ↦
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure (n + 1) :
        Measure (Real × Real)) (Set.diagonal Real))
    (g := fun _n : Nat ↦ (0 : ENNReal)) (h := data.badError)
    tendsto_const_nhds data.badError_tendsto_zero (fun _n ↦ bot_le)
    (fun n ↦
      canonicalChildRepeatedReducedAnnealed_diagonal_le_badError_of_actualAtlas
        data n)

/-! ## Compactness of the canonical annealed reduced laws -/

/-- Every realization-wise reduced child law lies in the common physical
frequency square. -/
theorem canonicalChildRepeatedReducedPerSite_compl_frequencySquare_eq_zero
    (n : Nat) (omega : RandomEnsemble.SampleSpace) :
    ((((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
          canonicalIIDMassPhaseEnsemble n omega).map
        forgetRankFrequencyTriple).map childRepeatedFrequencyProjection :
          FiniteMeasure (Real × Real)) : Measure (Real × Real))
      (childRepeatedFrequencySquare collisionFrequencyCeiling)ᶜ = 0 := by
  have hmarkedSupport :=
    canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_compl_uniformSupport_eq_zero
      canonicalIIDMassPhaseEnsemble n omega
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

/-- Barycentering preserves the same compact reduced-frequency carrier. -/
theorem canonicalChildRepeatedReducedAnnealed_compl_frequencySquare_eq_zero
    (n : Nat) :
    (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
      Measure (Real × Real))
      (childRepeatedFrequencySquare collisionFrequencyCeiling)ᶜ = 0 := by
  rw [canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply n
    (childRepeatedFrequencySquare_isClosed
      collisionFrequencyCeiling).measurableSet.compl]
  calc
    (∫⁻ omega,
        (((((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
              canonicalIIDMassPhaseEnsemble n omega).map
            forgetRankFrequencyTriple).map childRepeatedFrequencyProjection :
              FiniteMeasure (Real × Real)) : Measure (Real × Real))
          (childRepeatedFrequencySquare collisionFrequencyCeiling)ᶜ)
        ∂canonicalLaw) = ∫⁻ _omega, 0 ∂canonicalLaw := by
      apply lintegral_congr
      intro omega
      exact canonicalChildRepeatedReducedPerSite_compl_frequencySquare_eq_zero
        n omega
    _ = 0 := lintegral_zero

/-- The annealed reduced law inherits the canonical volume-independent mass
ceiling used in its Giry construction. -/
theorem canonicalChildRepeatedReducedAnnealed_mass_le (n : Nat) :
    (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).mass ≤
      childRepeatedCanonicalMassCeiling := by
  rw [← ENNReal.coe_le_coe]
  simp only [FiniteMeasure.ennreal_mass]
  rw [canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply n
    MeasurableSet.univ]
  calc
    (∫⁻ omega,
        (((((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
              canonicalIIDMassPhaseEnsemble n omega).map
            forgetRankFrequencyTriple).map
              childRepeatedFrequencyProjection :
                FiniteMeasure (Real × Real)) : Measure (Real × Real))
          Set.univ) ∂canonicalLaw) ≤
      ∫⁻ _omega,
        (childRepeatedCanonicalMassCeiling : ENNReal) ∂canonicalLaw := by
      apply lintegral_mono_ae
      filter_upwards [canonicalChildRepeatedReducedPerSite_mass_le_ae n]
        with omega homega
      simpa only [FiniteMeasure.ennreal_mass] using
        ENNReal.coe_le_coe.mpr homega
    _ = (childRepeatedCanonicalMassCeiling : ENNReal) := by
      rw [lintegral_const, measure_univ, mul_one]

/-- The canonical annealed reduced sequence has a genuine weakly convergent
cofinal subsequence before any atlas estimate is imposed. -/
theorem exists_canonicalChildRepeatedReducedAnnealed_weakCluster :
    ∃ target : FiniteMeasure (Real × Real),
      ∃ subsequence : Nat → Nat,
        StrictMono subsequence ∧
          Tendsto
            (fun j ↦
              canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
                (subsequence j + 1))
            atTop (nhds target) := by
  exact
    exists_weaklyConvergent_subsequence_of_compactSupport_of_mass_le
      (fun n ↦
        canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure (n + 1))
      childRepeatedCanonicalMassCeiling
      (childRepeatedFrequencySquare collisionFrequencyCeiling)
      (isCompact_Icc.prod isCompact_Icc)
      (fun n ↦ canonicalChildRepeatedReducedAnnealed_mass_le (n + 1))
      (fun n ↦
        canonicalChildRepeatedReducedAnnealed_compl_frequencySquare_eq_zero
          (n + 1))

/-! ## Exact planar domination and per-leg endpoints -/

/-- Any canonical annealed reduced weak limit along cofinal physical volumes
has the exact planar density ceiling supplied by the actual atlas sequence. -/
theorem canonicalChildRepeatedReducedAnnealed_weakLimit_le_volume_of_actualAtlas
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (index : Nat → Nat) (hindex : Tendsto index atTop atTop)
    (target : FiniteMeasure (Real × Real))
    (hlimit : Tendsto
      (fun j ↦ canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
        (index j + 1))
      atTop (nhds target)) :
    (target : Measure (Real × Real)) ≤
      data.regularCeiling • (volume : Measure (Real × Real)) := by
  apply finiteMeasure_le_smul_of_tendsto_of_apply_le_add_vanishingError
    (fun j ↦ canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
      (index j + 1))
    target hlimit (volume : Measure (Real × Real))
    data.regularCeiling data.regularCeiling_ne_top
    (data.badError ∘ index)
    (data.badError_tendsto_zero.comp hindex)
  intro j A hA
  exact canonicalChildRepeatedReducedAnnealed_apply_le_of_actualAtlas
    data (index j) hA

/-- The actual atlas sequence therefore constructs at least one canonical
annealed reduced weak cluster with a genuine `L∞` planar bound. -/
theorem exists_canonicalChildRepeatedReducedAnnealed_dominatedWeakCluster
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence) :
    ∃ target : FiniteMeasure (Real × Real),
      ∃ subsequence : Nat → Nat,
        StrictMono subsequence ∧
          Tendsto
            (fun j ↦
              canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
                (subsequence j + 1))
            atTop (nhds target) ∧
          (target : Measure (Real × Real)) ≤
            data.regularCeiling •
              (volume : Measure (Real × Real)) := by
  obtain ⟨target, subsequence, hmono, hlimit⟩ :=
    exists_canonicalChildRepeatedReducedAnnealed_weakCluster
  refine ⟨target, subsequence, hmono, hlimit, ?_⟩
  exact
    canonicalChildRepeatedReducedAnnealed_weakLimit_le_volume_of_actualAtlas
      data subsequence hmono.tendsto_atTop target hlimit

theorem canonicalChildRepeatedReducedAnnealed_weakLimit_parent_joint_le_volume
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (index : Nat → Nat) (hindex : Tendsto index atTop atTop)
    (target : FiniteMeasure (Real × Real))
    (hlimit : Tendsto
      (fun j ↦ canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
        (index j + 1))
      atTop (nhds target)) :
    Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv 0)
        (target : Measure (Real × Real)) ≤
      (data.regularCeiling / 2) •
        ((volume : Measure Real).prod (volume : Measure Real)) := by
  simpa [childRepeatedLegLebesgueConstant, div_eq_mul_inv] using
    map_childRepeatedLegFrequencyMismatchLinearEquiv_le_volume
      (target : Measure (Real × Real)) 0 data.regularCeiling
      (by
        simpa only [Measure.volume_eq_prod] using
          (canonicalChildRepeatedReducedAnnealed_weakLimit_le_volume_of_actualAtlas
            data index hindex target hlimit))

theorem canonicalChildRepeatedReducedAnnealed_weakLimit_child_joint_le_volume
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (index : Nat → Nat) (hindex : Tendsto index atTop atTop)
    (target : FiniteMeasure (Real × Real))
    (hlimit : Tendsto
      (fun j ↦ canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
        (index j + 1))
      atTop (nhds target))
    (leg : Fin 3) (hleg : leg ≠ 0) :
    Measure.map (childRepeatedLegFrequencyMismatchLinearEquiv leg)
        (target : Measure (Real × Real)) ≤
      data.regularCeiling •
        ((volume : Measure Real).prod (volume : Measure Real)) := by
  simpa [childRepeatedLegLebesgueConstant, hleg] using
    map_childRepeatedLegFrequencyMismatchLinearEquiv_le_volume
      (target : Measure (Real × Real)) leg data.regularCeiling
      (by
        simpa only [Measure.volume_eq_prod] using
          (canonicalChildRepeatedReducedAnnealed_weakLimit_le_volume_of_actualAtlas
            data index hindex target hlimit))

theorem canonicalChildRepeatedReducedAnnealed_weakLimit_parent_broadened_le_volume
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (index : Nat → Nat) (hindex : Tendsto index atTop atTop)
    (target : FiniteMeasure (Real × Real))
    (hlimit : Tendsto
      (fun j ↦ canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
        (index j + 1))
      atTop (nhds target))
    {T : Real} (hT : 0 < T) :
    Measure.map (childRepeatedLegFrequency 0)
        (broadenedResonanceMeasure target childRepeatedDecayMismatch
          measurable_childRepeatedDecayMismatch T hT :
            Measure (Real × Real)) ≤
      (data.regularCeiling / 2) • (volume : Measure Real) := by
  simpa [childRepeatedLegLebesgueConstant, div_eq_mul_inv] using
    map_childRepeatedLegFrequency_broadenedResonanceMeasure_le_volume
      target hT 0 data.regularCeiling
      (by
        simpa only [Measure.volume_eq_prod] using
          (canonicalChildRepeatedReducedAnnealed_weakLimit_le_volume_of_actualAtlas
            data index hindex target hlimit))

theorem canonicalChildRepeatedReducedAnnealed_weakLimit_child_broadened_le_volume
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (index : Nat → Nat) (hindex : Tendsto index atTop atTop)
    (target : FiniteMeasure (Real × Real))
    (hlimit : Tendsto
      (fun j ↦ canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
        (index j + 1))
      atTop (nhds target))
    {T : Real} (hT : 0 < T) (leg : Fin 3) (hleg : leg ≠ 0) :
    Measure.map (childRepeatedLegFrequency leg)
        (broadenedResonanceMeasure target childRepeatedDecayMismatch
          measurable_childRepeatedDecayMismatch T hT :
            Measure (Real × Real)) ≤
      data.regularCeiling • (volume : Measure Real) := by
  simpa [childRepeatedLegLebesgueConstant, hleg] using
    map_childRepeatedLegFrequency_broadenedResonanceMeasure_le_volume
      target hT leg data.regularCeiling
      (by
        simpa only [Measure.volume_eq_prod] using
          (canonicalChildRepeatedReducedAnnealed_weakLimit_le_volume_of_actualAtlas
            data index hindex target hlimit))

/-! ## Fixed-test inverse-sensitivity adapter -/

/-- The existing inverse-volume sensitivity theorem has exactly the metric
form required by the annealed-to-quenched bridge for each fixed test.  The
almost-everywhere set can still depend on `test`; obtaining one sample that
works for every bounded-continuous test requires a determining-class step. -/
theorem canonicalChildRepeatedReduced_test_dist_tendsto_ae_of_inverseSensitivity
    (test : (Real × Real) →ᵇ NNReal) (K : NNReal) (hK : 0 < K)
    (hrange : ∀ n x,
      finChildRepeatedReducedRawTest n test x ∈ Set.Icc 0 1)
    (hsensitivity : ∀ n, HasFinBoundedDifferences
      (finChildRepeatedReducedRawTest n test)
      (fun _ : Fin (n + 2) ↦ K / ((n + 2 : Nat) : NNReal))) :
    ∀ᵐ omega ∂canonicalLaw,
      Tendsto
        (fun n ↦ dist
          ((((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
              canonicalIIDMassPhaseEnsemble n omega).map
            forgetRankFrequencyTriple).map
              childRepeatedFrequencyProjection).testAgainstNN test)
          ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN
            test))
        atTop (nhds 0) := by
  filter_upwards
    [canonicalChildRepeatedReducedRawTest_tendsto_annealed_ae_of_inverseSensitivity
      test K hK hrange hsensitivity] with omega homega
  simpa only [
    canonicalChildRepeatedReducedRawTest_eq_testAgainstNN,
    NNReal.dist_eq] using homega

/-! ## Quenched hybrid-lift closure through the existing self-averaging gate -/

/-- The actual atlas estimate discharges the entire annealed part of the
quenched weak-test closure.  What remains is exactly the existing pathwise
all-test self-averaging premise `hclose`. -/
theorem ChildRepeatedScalarClusterHybridLiftData.reduced_le_volume_of_actualAtlas
    {omega : RandomEnsemble.SampleSpace}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      canonicalIIDMassPhaseEnsemble omega size scalarTarget)
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (atlasIndex : Nat → Nat)
    (hvolume : ∀ j,
      size (lift.subsequence j) = atlasIndex j + 1)
    (hindex : Tendsto atlasIndex atTop atTop)
    (hclose : ∀ f : (Real × Real) →ᵇ NNReal,
      Tendsto
        (fun j ↦ dist
          (((canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
              canonicalIIDMassPhaseEnsemble
              (size (lift.subsequence j)) omega).map
            childRepeatedFrequencyProjection).testAgainstNN f)
          ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
              (size (lift.subsequence j))).testAgainstNN f))
        atTop (nhds 0)) :
    ((((lift.markedTarget.map forgetRankFrequencyTriple).map
        childRepeatedFrequencyProjection :
      FiniteMeasure (Real × Real)) : Measure (Real × Real))) ≤
      data.regularCeiling • (volume : Measure (Real × Real)) := by
  apply
    childRepeatedScalarClusterHybridLift_reduced_le_volume_of_annealed_of_testAgainstNN_dist
      lift data.regularCeiling data.regularCeiling_ne_top
      (data.badError ∘ atlasIndex)
      (data.badError_tendsto_zero.comp hindex)
  · intro j A hA
    rw [hvolume j]
    exact canonicalChildRepeatedReducedAnnealed_apply_le_of_actualAtlas
      data (atlasIndex j) hA
  · exact hclose

/-- All marked leg joint bounds now follow with the exact determinant
constant; no additional kernel-identification premise is needed. -/
theorem ChildRepeatedScalarClusterHybridLiftData.map_markedJoint_le_volume_of_actualAtlas
    {omega : RandomEnsemble.SampleSpace}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      canonicalIIDMassPhaseEnsemble omega size scalarTarget)
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (atlasIndex : Nat → Nat)
    (hvolume : ∀ j,
      size (lift.subsequence j) = atlasIndex j + 1)
    (hindex : Tendsto atlasIndex atTop atTop)
    (hclose : ∀ f : (Real × Real) →ᵇ NNReal,
      Tendsto
        (fun j ↦ dist
          (((canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
              canonicalIIDMassPhaseEnsemble
              (size (lift.subsequence j)) omega).map
            childRepeatedFrequencyProjection).testAgainstNN f)
          ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
              (size (lift.subsequence j))).testAgainstNN f))
        atTop (nhds 0))
    (leg : Fin 3) :
    Measure.map (childRepeatedMarkedFrequencyMismatchCoordinates leg)
        (lift.markedTarget : Measure (Fin 3 → RankFrequencyMark)) ≤
      (data.regularCeiling * childRepeatedLegLebesgueConstant leg) •
        ((volume : Measure Real).prod (volume : Measure Real)) := by
  exact
    map_childRepeatedMarkedFrequencyMismatchCoordinates_le_volume_of_support
      lift.markedTarget lift.frequencyDiagonal leg data.regularCeiling
      (by
        simpa only [FiniteMeasure.toMeasure_map, Measure.volume_eq_prod] using
          (ChildRepeatedScalarClusterHybridLiftData.reduced_le_volume_of_actualAtlas
            lift data atlasIndex hvolume hindex hclose))

/-- The marked broadened marginal is consequently time-uniform on every leg
with factor `1/2` for the parent and `1` for either child. -/
theorem ChildRepeatedScalarClusterHybridLiftData.map_markedLeg_broadened_le_volume_of_actualAtlas
    {omega : RandomEnsemble.SampleSpace}
    {size : Nat → Nat} {scalarTarget : FiniteMeasure Real}
    (lift : ChildRepeatedScalarClusterHybridLiftData
      canonicalIIDMassPhaseEnsemble omega size scalarTarget)
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (atlasIndex : Nat → Nat)
    (hvolume : ∀ j,
      size (lift.subsequence j) = atlasIndex j + 1)
    (hindex : Tendsto atlasIndex atTop atTop)
    (hclose : ∀ f : (Real × Real) →ᵇ NNReal,
      Tendsto
        (fun j ↦ dist
          (((canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
              canonicalIIDMassPhaseEnsemble
              (size (lift.subsequence j)) omega).map
            childRepeatedFrequencyProjection).testAgainstNN f)
          ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure
              (size (lift.subsequence j))).testAgainstNN f))
        atTop (nhds 0))
    {T : Real} (hT : 0 < T) (leg : Fin 3) :
    Measure.map (markedLegFrequency leg)
        (broadenedResonanceMeasure lift.markedTarget
          (markedFrequencyMismatch decayInteractionSign)
          (measurable_markedFrequencyMismatch decayInteractionSign)
          T hT : Measure (Fin 3 → RankFrequencyMark)) ≤
      (data.regularCeiling * childRepeatedLegLebesgueConstant leg) •
        (volume : Measure Real) := by
  exact
    map_childRepeatedMarkedLeg_broadenedResonanceMeasure_le_volume_of_support
      lift.markedTarget lift.frequencyDiagonal hT leg data.regularCeiling
      (by
        simpa only [FiniteMeasure.toMeasure_map, Measure.volume_eq_prod] using
          (ChildRepeatedScalarClusterHybridLiftData.reduced_le_volume_of_actualAtlas
            lift data atlasIndex hvolume hindex hclose))

end

end ArchonPhysics.CanonicalChildRepeatedFrequencyMismatchJointClosure
