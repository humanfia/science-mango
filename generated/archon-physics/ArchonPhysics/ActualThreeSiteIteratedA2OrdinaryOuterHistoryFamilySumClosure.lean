import ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily

/-!
# The four-term ordinary outer-history sum on three sites

This file sums the four signed actual-A2 weak-coupling accumulations indexed
by `Fin 2 × Fin 2` in
`ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily`.  The signed qualifier
refers to the measurable signed-frame weight inside each channel; the
accumulation itself is the nonnegative time integral of its norm.

Every summand already has an end-to-end fixed-volume theorem.  A finite-sum
`Tendsto` argument therefore proves that the whole displayed four-term sum
vanishes as `g → 0+`, with no new spectrum, Jacobian, or acoustic hypotheses.
The result still concerns only this explicit ordinary outer-history family.
It is neither a sum over all A2 histories nor a closure of the complete
collision operator.
-/

namespace
  ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamilySumClosure

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

/-! ## The explicit four-term aggregate -/

/-- The signed actual-A2 weak-coupling accumulation summed over the four
ordinary outer histories.  Both binary choices are summed over by the
`Fintype` sum on `Fin 2 × Fin 2`. -/
def actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa : Real) (radius : Omega → Lattice.Site 3 → Real)
    (g : Real) : Real :=
  ∑ index : ThreeSiteOrdinaryOuterHistoryIndex,
    actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
      .outer kappa radius firstPositivePhysicalModeThree
      (threeSiteOrdinaryOuterHistoryTerm index) g

@[simp] theorem
    actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation_eq_sum
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa : Real) (radius : Omega → Lattice.Site 3 → Real)
    (g : Real) :
    actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
        ensemble kappa radius g =
      ∑ index : ThreeSiteOrdinaryOuterHistoryIndex,
        actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
          .outer kappa radius firstPositivePhysicalModeThree
          (threeSiteOrdinaryOuterHistoryTerm index) g := rfl

/-! ## Family certificate -/

/-- A reusable family certificate is exactly one signed `L1` Fourier
certificate for each of the four displayed histories. -/
abbrev ActualThreeSiteOrdinaryOuterHistorySignedL1FamilyCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa : Real) (radius : Omega → Lattice.Site 3 → Real) :=
  ∀ index : ThreeSiteOrdinaryOuterHistoryIndex,
    ActualSignedIteratedA2StaticL1FourierCertificate ensemble .outer kappa
      radius firstPositivePhysicalModeThree
      (threeSiteOrdinaryOuterHistoryTerm index)

/-- The four per-history certificates packaged as a single dependent family.
Its assumptions are only the common measurable bounded radii and `R ≥ 0`. -/
def actualThreeSiteOrdinaryOuterHistorySignedL1FamilyCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 3 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    ActualThreeSiteOrdinaryOuterHistorySignedL1FamilyCertificate ensemble
      kappa radius :=
  fun index =>
    actualThreeSiteOrdinaryOuterHistorySignedL1Certificate ensemble index
      kappa R hR radius hradiusMeasurable hradiusBound

/-- The end-to-end result for one indexed family member, retaining both its
signed `L1` certificate and its weak-coupling limit. -/
theorem actualThreeSiteOrdinaryOuterHistorySignedPerTerm_endToEnd
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 3 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    Nonempty
        (ActualSignedIteratedA2StaticL1FourierCertificate ensemble .outer
          kappa radius firstPositivePhysicalModeThree
          (threeSiteOrdinaryOuterHistoryTerm index)) ∧
      Tendsto
        (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
          .outer kappa radius firstPositivePhysicalModeThree
          (threeSiteOrdinaryOuterHistoryTerm index))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    ⟨⟨actualThreeSiteOrdinaryOuterHistorySignedL1Certificate ensemble index
        kappa R hR radius hradiusMeasurable hradiusBound⟩,
      tendsto_actualThreeSiteOrdinaryOuterHistorySignedWeakCoupling ensemble
        index kappa R hR radius hradiusMeasurable hradiusBound⟩

/-! ## Fixed-volume closure of the complete displayed family -/

/-- The whole four-term family sum vanishes at fixed volume as `g → 0+`.
There are no exposed spectrum, Jacobian, transversality, or acoustic
assumptions: those channel-specific obligations were discharged once and for
all by the per-term end-to-end theorem. -/
theorem
    tendsto_actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 3 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    Tendsto
      (actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
        ensemble kappa radius)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  unfold
    actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
  simpa using
    tendsto_finsetSum Finset.univ (fun index _hindex =>
      (actualThreeSiteOrdinaryOuterHistorySignedPerTerm_endToEnd ensemble index
        kappa R hR radius hradiusMeasurable hradiusBound).2)

/-- Packaged family endpoint: all four signed `L1` certificates exist and
the sum of the corresponding weak-coupling accumulations tends to zero. -/
theorem actualThreeSiteOrdinaryOuterHistoryFamilySignedFixedVolume_endToEnd
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 3 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    Nonempty
        (ActualThreeSiteOrdinaryOuterHistorySignedL1FamilyCertificate ensemble
          kappa radius) ∧
      Tendsto
        (actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
          ensemble kappa radius)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    ⟨⟨actualThreeSiteOrdinaryOuterHistorySignedL1FamilyCertificate ensemble
        kappa R hR radius hradiusMeasurable hradiusBound⟩,
      tendsto_actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
        ensemble kappa R hR radius hradiusMeasurable hradiusBound⟩

end

end
  ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamilySumClosure
