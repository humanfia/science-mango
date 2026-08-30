import ArchonPhysics.PhyslibFPUTActualBranchingA1IntervalSelector
import ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall

/-!
# Actual branching heterogeneous A1 compact small-ball bound

Every denominator selected by the actual branching module is a contiguous
sum of genuine local A1 charts, but its vertices may have different observed
output modes.  This file develops the corresponding heterogeneous scalar
fiber atlas.

For one interval, the strict vertical derivative is exactly the sum of the
actual vertex Jacobians.  On an explicitly supplied compact set K, regularity
of every selected local chart and the honest noncancellation input

  j0 <= |sum J_vertex|

produce a finite inverse-function atlas.  Measurability and the sharp 5/2
one-site mass density are derived from existing modules.

Applying this independently to the finite actual branching selector gives a
full-history small-denominator bound.  The linear-in-threshold coefficient is
the sum of the actual atlas coefficients and is at most

  order! * order^2 * (largest selected coefficient).

The compact-complement union is charged once.  No Jacobian lower bound is
claimed to follow from the random-mass law; no phase independence, re-Haar,
Markov/RPA closure, or recollision estimate is used.
-/

namespace ArchonPhysics.PhyslibFPUTActualBranchingA1CompactSmallBall

open scoped BigOperators ENNReal

open ArchonPhysics
open ArchonPhysics.FiniteHistorySmallDenominatorUnionBound
open ArchonPhysics.FreeFPUTBranchingHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalCompactSmallBall
open ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalUnionBound
open ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTActualBranchingA1IntervalSelector
open ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Function MeasureTheory Set

noncomputable section

/-! ## Heterogeneous actual interval calculus -/

/-- Sum of actual A1 charts whose observed output mode may vary with the
vertex. -/
def actualA1VertexListPairMismatchChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (vertices : List (ActualA1Vertex N))
    (pair : Real × Real) : Real :=
  ∑ index : Fin vertices.length,
    physlibA1PairMismatchChart fixed site₁ site₂
      (vertices.get index).observed (vertices.get index).term pair

/-- Sum of the genuine actual vertical Jacobians of a heterogeneous list. -/
def actualA1VertexListVerticalJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (vertices : List (ActualA1Vertex N))
    (pair : Real × Real) : Real :=
  ∑ index : Fin vertices.length,
    physlibA1PairMismatchVerticalJacobian fixed site₁ site₂
      (vertices.get index).observed (vertices.get index).term pair

/-- Common differentiability source of all vertices in a heterogeneous list.
The physical pair-support interior remains explicit. -/
def actualA1VertexListDifferentiabilitySource
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (vertices : List (ActualA1Vertex N)) : Set (Real × Real) :=
  {pair | pair ∈ interior iidMassPairSupport ∧
    ∀ vertex ∈ vertices,
      pair ∈ physlibA1PairMismatchDifferentiabilitySource
        fixed site₁ site₂ vertex.observed vertex.term}

/-- Heterogeneous list charts are measurable because every actual local A1
chart is measurable. -/
theorem measurable_actualA1VertexListPairMismatchChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (vertices : List (ActualA1Vertex N)) :
    Measurable
      (actualA1VertexListPairMismatchChart
        fixed site₁ site₂ vertices) := by
  unfold actualA1VertexListPairMismatchChart
  apply Finset.measurable_sum
  intro index hindex
  exact measurable_physlibA1PairMismatchChart
    fixed site₁ site₂ (vertices.get index).observed
      (vertices.get index).term

/-- Strict derivative of a heterogeneous list is its total actual vertical
Jacobian.  This is the cancellation-sensitive identity used below. -/
theorem hasStrictDerivAt_actualA1VertexListPairMismatchFiber
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (vertices : List (ActualA1Vertex N))
    {pair : Real × Real}
    (hregular : pair ∈
      actualA1VertexListDifferentiabilitySource
        fixed site₁ site₂ vertices) :
    HasStrictDerivAt
      (fun second =>
        actualA1VertexListPairMismatchChart
          fixed site₁ site₂ vertices (pair.1, second))
      (actualA1VertexListVerticalJacobian
        fixed site₁ site₂ vertices pair) pair.2 := by
  unfold actualA1VertexListPairMismatchChart
    actualA1VertexListVerticalJacobian
  apply HasStrictDerivAt.fun_sum
  intro index hindex
  exact hasStrictDerivAt_physlibA1PairMismatchFiber
    fixed hsite (vertices.get index).observed (vertices.get index).term
      (hregular.2 (vertices.get index) (List.get_mem vertices index))

/-- Differentiability source of one selected heterogeneous interval. -/
def actualA1VertexIntervalDifferentiabilitySource
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (history : List (ActualA1Vertex N))
    (interval : OrderedHistoryInterval history.length) :
    Set (Real × Real) :=
  actualA1VertexListDifferentiabilitySource fixed site₁ site₂
    (interval.block history)

/-- The existing interval chart is the heterogeneous list chart of its
selected block. -/
theorem actualA1VertexIntervalPairMismatchChart_eq_listChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (history : List (ActualA1Vertex N))
    (interval : OrderedHistoryInterval history.length)
    (pair : Real × Real) :
    actualA1VertexIntervalPairMismatchChart
        fixed site₁ site₂ history interval pair =
      actualA1VertexListPairMismatchChart
        fixed site₁ site₂ (interval.block history) pair := by
  let block := interval.block history
  let phase : ActualA1Vertex N → Real := fun vertex =>
    physlibA1PairMismatchChart fixed site₁ site₂
      vertex.observed vertex.term pair
  change (block.map phase).sum =
    ∑ index : Fin block.length, phase (block.get index)
  rw [← List.sum_ofFn,
    List.ofFn_comp' (List.get block) phase, List.ofFn_get]

/-- The interval Jacobian is the heterogeneous list Jacobian of the same
block. -/
theorem actualA1VertexIntervalVerticalJacobian_eq_listJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (history : List (ActualA1Vertex N))
    (interval : OrderedHistoryInterval history.length)
    (pair : Real × Real) :
    actualA1VertexIntervalVerticalJacobian
        fixed site₁ site₂ history interval pair =
      actualA1VertexListVerticalJacobian
        fixed site₁ site₂ (interval.block history) pair := by
  let block := interval.block history
  let jacobian : ActualA1Vertex N → Real := fun vertex =>
    physlibA1PairMismatchVerticalJacobian fixed site₁ site₂
      vertex.observed vertex.term pair
  change (block.map jacobian).sum =
    ∑ index : Fin block.length, jacobian (block.get index)
  rw [← List.sum_ofFn,
    List.ofFn_comp' (List.get block) jacobian, List.ofFn_get]

/-- The heterogeneous interval chart is measurable. -/
theorem measurable_actualA1VertexIntervalPairMismatchChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (history : List (ActualA1Vertex N))
    (interval : OrderedHistoryInterval history.length) :
    Measurable
      (actualA1VertexIntervalPairMismatchChart
        fixed site₁ site₂ history interval) := by
  rw [show actualA1VertexIntervalPairMismatchChart
      fixed site₁ site₂ history interval =
    actualA1VertexListPairMismatchChart
      fixed site₁ site₂ (interval.block history) by
        funext pair
        exact actualA1VertexIntervalPairMismatchChart_eq_listChart
          fixed site₁ site₂ history interval pair]
  exact measurable_actualA1VertexListPairMismatchChart
    fixed site₁ site₂ (interval.block history)

/-- Strict derivative of an interval is exactly the sum of its actual
vertical Jacobians, with no common-output assumption. -/
theorem hasStrictDerivAt_actualA1VertexIntervalPairMismatchFiber
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (history : List (ActualA1Vertex N))
    (interval : OrderedHistoryInterval history.length)
    {pair : Real × Real}
    (hregular : pair ∈
      actualA1VertexIntervalDifferentiabilitySource
        fixed site₁ site₂ history interval) :
    HasStrictDerivAt
      (fun second =>
        actualA1VertexIntervalPairMismatchChart
          fixed site₁ site₂ history interval (pair.1, second))
      (actualA1VertexIntervalVerticalJacobian
        fixed site₁ site₂ history interval pair) pair.2 := by
  simpa [actualA1VertexIntervalDifferentiabilitySource,
    actualA1VertexIntervalPairMismatchChart_eq_listChart,
    actualA1VertexIntervalVerticalJacobian_eq_listJacobian] using
      hasStrictDerivAt_actualA1VertexListPairMismatchFiber
        fixed hsite (interval.block history) hregular

/-- A nonzero total heterogeneous Jacobian gives a local injective scalar
fiber patch. -/
theorem exists_actualA1VertexIntervalPairFiber_localInjectivePatch
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (history : List (ActualA1Vertex N))
    (interval : OrderedHistoryInterval history.length)
    {pair : Real × Real}
    (hregular : pair ∈
      actualA1VertexIntervalDifferentiabilitySource
        fixed site₁ site₂ history interval)
    (hjac : actualA1VertexIntervalVerticalJacobian
      fixed site₁ site₂ history interval pair ≠ 0) :
    ∃ patch : Set Real,
      pair.2 ∈ patch ∧ IsOpen patch ∧ MeasurableSet patch ∧
      patch ⊆ massSupport ∧
      InjOn
        (fun second => actualA1VertexIntervalPairMismatchChart
          fixed site₁ site₂ history interval (pair.1, second)) patch := by
  let jacobian := actualA1VertexIntervalVerticalJacobian
    fixed site₁ site₂ history interval pair
  let derivativeEquiv : Real ≃L[Real] Real :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 jacobian hjac)
  have hequiv : (derivativeEquiv : Real →L[Real] Real) =
      ContinuousLinearMap.toSpanSingleton Real jacobian := by
    apply ContinuousLinearMap.ext
    intro x
    simp [derivativeEquiv, jacobian, mul_comm]
  have hstrict :=
    hasStrictDerivAt_actualA1VertexIntervalPairMismatchFiber
      fixed hsite history interval hregular
  have hstrictEquiv : HasStrictFDerivAt
      (fun second => actualA1VertexIntervalPairMismatchChart
        fixed site₁ site₂ history interval (pair.1, second))
      (derivativeEquiv : Real →L[Real] Real) pair.2 := by
    rw [hequiv]
    exact hstrict
  let localChart : OpenPartialHomeomorph Real Real :=
    hstrictEquiv.toOpenPartialHomeomorph _
  have hpointSource : pair.2 ∈ localChart.source :=
    hstrictEquiv.mem_toOpenPartialHomeomorph_source
  have hsecondInterior : pair.2 ∈ interior massSupport := by
    have hpairInterior := hregular.1
    rw [iidMassPairSupport, interior_prod_eq] at hpairInterior
    exact hpairInterior.2
  let patch := localChart.source ∩ interior massSupport
  refine ⟨patch, ⟨hpointSource, hsecondInterior⟩,
    localChart.open_source.inter isOpen_interior,
    (localChart.open_source.inter isOpen_interior).measurableSet, ?_, ?_⟩
  · intro second hsecond
    exact interior_subset hsecond.2
  · exact localChart.injOn.mono inter_subset_left

/-! ## One heterogeneous compact atlas -/

/-- Compact heterogeneous interval atlas under the sole noncancellation
bound on the total actual Jacobian sum, together with displayed compactness
and differentiability-domain conditions. -/
theorem exists_atlasCard_actualA1VertexIntervalPairFiberCompact
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (history : List (ActualA1Vertex N))
    (interval : OrderedHistoryInterval history.length)
    (first : Real) (K : Set Real) (hK : IsCompact K)
    (hKregular : ∀ second ∈ K,
      (first, second) ∈
        actualA1VertexIntervalDifferentiabilitySource
          fixed site₁ site₂ history interval)
    {j₀ : Real} (hj₀ : 0 < j₀)
    (hjac : ∀ second ∈ K, j₀ ≤
      |actualA1VertexIntervalVerticalJacobian
        fixed site₁ site₂ history interval (first, second)|) :
    ∃ atlasCard : Nat,
      ∀ {target : Set Real}, MeasurableSet target →
        Measure.map
            (fun second => actualA1VertexIntervalPairMismatchChart
              fixed site₁ site₂ history interval (first, second))
            (massCoordinateLaw.restrict K) target ≤
          ((atlasCard : ENNReal) *
            ((5 / 2 : ENNReal) * (ENNReal.ofReal j₀)⁻¹)) *
              (volume : Measure Real) target := by
  classical
  let chart : Real → Real := fun second =>
    actualA1VertexIntervalPairMismatchChart
      fixed site₁ site₂ history interval (first, second)
  let derivative : Real → (Real →L[Real] Real) := fun second =>
    ContinuousLinearMap.toSpanSingleton Real
      (actualA1VertexIntervalVerticalJacobian
        fixed site₁ site₂ history interval (first, second))
  have hchart : Measurable chart :=
    (measurable_actualA1VertexIntervalPairMismatchChart
      fixed site₁ site₂ history interval).comp
        (measurable_const.prodMk measurable_id)
  have hlocal : ∀ point : K, ∃ patch : Set Real,
      IsOpen patch ∧ point.1 ∈ patch ∧ InjOn chart patch := by
    intro point
    have hregular := hKregular point.1 point.2
    have hnonzero : actualA1VertexIntervalVerticalJacobian
        fixed site₁ site₂ history interval (first, point.1) ≠ 0 := by
      exact abs_pos.mp (hj₀.trans_le (hjac point.1 point.2))
    obtain ⟨patch, hpoint, hopen, _hmeasurable, _hsupport, hinjective⟩ :=
      exists_actualA1VertexIntervalPairFiber_localInjectivePatch
        fixed hsite history interval hregular hnonzero
    exact ⟨patch, hopen, hpoint, hinjective⟩
  choose localPatch hopen hmem hinjective using hlocal
  obtain ⟨atlas, hcover⟩ := hK.elim_finite_subcover localPatch hopen (by
    intro point hpoint
    rw [mem_iUnion]
    exact ⟨⟨point, hpoint⟩, hmem ⟨point, hpoint⟩⟩)
  let AtlasIndex := {point : K // point ∈ atlas}
  let patch : AtlasIndex → Set Real := fun index =>
    K ∩ localPatch index.1
  have hpatch : ∀ index : AtlasIndex, MeasurableSet (patch index) := by
    intro index
    exact hK.isClosed.measurableSet.inter (hopen index.1).measurableSet
  have hcoverK : K ⊆ ⋃ index : AtlasIndex, patch index := by
    intro second hsecond
    rcases mem_iUnion₂.mp (hcover hsecond) with
      ⟨center, hcenter, hsecondPatch⟩
    rw [mem_iUnion]
    exact ⟨⟨center, hcenter⟩, hsecond, hsecondPatch⟩
  have hderivative : ∀ index : AtlasIndex, ∀ second ∈ patch index,
      HasFDerivWithinAt chart (derivative second) (patch index) second := by
    intro index second hsecond
    have hstrict :=
      hasStrictDerivAt_actualA1VertexIntervalPairMismatchFiber
        fixed hsite history interval (hKregular second hsecond.1)
    exact hstrict.hasDerivAt.hasFDerivAt.hasFDerivWithinAt
  have hsource : ∀ index : AtlasIndex,
      massCoordinateLaw.restrict (patch index) ≤
        (5 / 2 : ENNReal) •
          (volume : Measure Real).restrict (patch index) := by
    intro index
    calc
      massCoordinateLaw.restrict (patch index) ≤
          ((5 / 2 : ENNReal) •
            (volume : Measure Real)).restrict (patch index) :=
        Measure.restrict_mono_measure
          massCoordinateLaw_le_fiveHalves_smul_volume _
      _ = (5 / 2 : ENNReal) •
          (volume : Measure Real).restrict (patch index) := by
        rw [Measure.restrict_smul]
  have hmain := scalarFinitePatchAtlas_map_restrict_and_full_apply_le
    massCoordinateLaw K hK.isClosed.measurableSet chart hchart patch hpatch
      hcoverK (fun _index => derivative)
      (fun index => hderivative index)
      (fun index => (hinjective index.1).mono inter_subset_right)
      (fun _index : AtlasIndex => j₀) (fun _ => hj₀)
      (fun _index second hsecond => by
        simpa [derivative] using hjac second hsecond.1)
      (fun _index : AtlasIndex => (5 / 2 : ENNReal)) hsource
  refine ⟨atlas.card, ?_⟩
  intro target htarget
  simpa [AtlasIndex, chart] using hmain.1 htarget

/-- Package the preceding derived atlas in the generic finite-union
interface. -/
theorem exists_ordinaryGardenCoordinateCompactAtlas_of_actualA1Interval
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (history : List (ActualA1Vertex N))
    (interval : OrderedHistoryInterval history.length)
    (first : Real) (K : Set Real) (hK : IsCompact K)
    (hKregular : ∀ second ∈ K,
      (first, second) ∈
        actualA1VertexIntervalDifferentiabilitySource
          fixed site₁ site₂ history interval)
    {j₀ : Real} (hj₀ : 0 < j₀)
    (hjac : ∀ second ∈ K, j₀ ≤
      |actualA1VertexIntervalVerticalJacobian
        fixed site₁ site₂ history interval (first, second)|) :
    ∃ certificate : OrdinaryGardenCoordinateCompactAtlas
        (fun second => actualA1VertexIntervalPairMismatchChart
          fixed site₁ site₂ history interval (first, second)),
      certificate.compactSet = K ∧ certificate.jacLower = j₀ := by
  obtain ⟨atlasCard, hregular⟩ :=
    exists_atlasCard_actualA1VertexIntervalPairFiberCompact
      fixed hsite history interval first K hK hKregular hj₀ hjac
  let chart : Real → Real := fun second =>
    actualA1VertexIntervalPairMismatchChart
      fixed site₁ site₂ history interval (first, second)
  have hchart : Measurable chart :=
    (measurable_actualA1VertexIntervalPairMismatchChart
      fixed site₁ site₂ history interval).comp
        (measurable_const.prodMk measurable_id)
  let certificate : OrdinaryGardenCoordinateCompactAtlas chart :=
    { compactSet := K
      isCompact_compactSet := hK
      atlasCard := atlasCard
      jacLower := j₀
      jacLower_pos := hj₀
      coordinate_measurable := hchart
      map_restrict_le := hregular }
  exact ⟨certificate, rfl, rfl⟩

/-! ## Full actual branching union -/

/-- Full actual branching small-denominator event along the common mass path
reconstructed by the occurrence-dependent fibers. -/
def actualA1BranchingSmallDenominatorEvent
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (gamma : Real) : Set Real :=
  {second | ∃ delta ∈ branchingHistoryDenominators tree.shape
      (randomEigenmodeBinaryTreeA1PhaseAssignment
        (fiber.massFamily second) tree),
      |delta| < gamma}

/-- The algebraic covers theorem places the full branching event inside the
finite heterogeneous-coordinate event. -/
theorem actualA1BranchingSmallDenominatorEvent_subset_finite
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (gamma : Real) :
    actualA1BranchingSmallDenominatorEvent tree fiber gamma ⊆
      finiteSmallDenominatorEvent
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber) gamma := by
  intro second hsecond
  rcases hsecond with ⟨delta, hdelta, hsmall⟩
  obtain ⟨index, hindex⟩ :=
    actualA1BranchingOccurrenceFiberCoordinate_covers
      tree fiber second delta hdelta
  rw [mem_finiteSmallDenominatorEvent_iff]
  exact ⟨index, by simpa [← hindex] using hsmall⟩

/-- One compact-atlas certificate for every genuine actual branching
interval gives the full-history union bound. -/
theorem measure_actualA1BranchingSmallDenominatorEvent_le_compactAtlas
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index))
    (gamma : Real) :
    massCoordinateLaw
        (actualA1BranchingSmallDenominatorEvent tree fiber gamma) ≤
      finiteCoordinateCompactAtlasRegularCoefficient
          (actualA1BranchingOccurrenceFiberCoordinate tree fiber)
          certificate * ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (finiteCoordinateCompactAtlasBadEvent
            (actualA1BranchingOccurrenceFiberCoordinate tree fiber)
            certificate) := by
  exact measure_event_le_finiteCoordinateCompactAtlas
    (actualA1BranchingSmallDenominatorEvent tree fiber gamma)
    (actualA1BranchingOccurrenceFiberCoordinate tree fiber)
    certificate gamma
    (actualA1BranchingSmallDenominatorEvent_subset_finite
      tree fiber gamma)

/-- Compact-complement union for occurrence-dependent good sets. -/
def actualA1BranchingOccurrenceCompactBadEvent
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (K : ActualA1BranchingIntervalIndex tree → Set Real) : Set Real :=
  ⋃ index, (K index)ᶜ

/-- The largest actual per-coordinate atlas coefficient.  It is derived from
the finite certificate family, not postulated as a uniform transversality
constant. -/
def actualA1BranchingCompactAtlasUniformBudget
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index)) :
    ENNReal :=
  Finset.univ.sup fun index => (certificate index).regularCoefficient

/-- Every selected coefficient is bounded by the derived finite maximum. -/
theorem actualA1BranchingCompactAtlasRegularCoefficient_le_uniformBudget
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index))
    (index : ActualA1BranchingIntervalIndex tree) :
    (certificate index).regularCoefficient ≤
      actualA1BranchingCompactAtlasUniformBudget
        tree fiber certificate := by
  classical
  exact Finset.le_sup
    (f := fun next : ActualA1BranchingIntervalIndex tree =>
      (certificate next).regularCoefficient)
    (b := index) (Finset.mem_univ index)

/-- The exact finite coefficient sum costs at most order! times order squared
copies of its derived largest coefficient. -/
theorem actualA1BranchingCompactAtlasRegularCoefficient_le_factorial_sq
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index)) :
    finiteCoordinateCompactAtlasRegularCoefficient
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber)
        certificate ≤
      (tree.shape.order.factorial *
        (tree.shape.order * tree.shape.order) : Nat) *
          actualA1BranchingCompactAtlasUniformBudget
            tree fiber certificate := by
  calc
    finiteCoordinateCompactAtlasRegularCoefficient
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber)
        certificate ≤
      ∑ _index : ActualA1BranchingIntervalIndex tree,
        actualA1BranchingCompactAtlasUniformBudget tree fiber certificate := by
          unfold finiteCoordinateCompactAtlasRegularCoefficient
          gcongr with index
          exact
            actualA1BranchingCompactAtlasRegularCoefficient_le_uniformBudget
              tree fiber certificate index
    _ = (Fintype.card (ActualA1BranchingIntervalIndex tree) : ENNReal) *
        actualA1BranchingCompactAtlasUniformBudget
          tree fiber certificate := by simp
    _ ≤ (tree.shape.order.factorial *
          (tree.shape.order * tree.shape.order) : Nat) *
        actualA1BranchingCompactAtlasUniformBudget
          tree fiber certificate := by
      gcongr
      exact_mod_cast card_actualA1BranchingIntervalIndex_le
        (fiber.massFamily 0) tree

/-- The constructed certificate coefficient exposes its actual atlas
multiplicity and supplied Jacobian threshold. -/
theorem ordinaryGardenCoefficient_eq_atlasCard_mul_jacobian
    {coordinate : Real → Real}
    (certificate : OrdinaryGardenCoordinateCompactAtlas coordinate)
    {j₀ : Real} (hjac : certificate.jacLower = j₀) :
    certificate.regularCoefficient =
      (certificate.atlasCard : ENNReal) *
        ((5 / 2 : ENNReal) * (ENNReal.ofReal j₀)⁻¹) := by
  simp [OrdinaryGardenCoordinateCompactAtlas.regularCoefficient, hjac]

/-- The compactness, regularity-domain, and total-Jacobian hypotheses build
all occurrence certificates.  The only noncancellation premise is the
displayed lower bound on each heterogeneous sum. -/
theorem exists_actualA1BranchingOccurrenceCompactAtlasCertificates
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (K : ActualA1BranchingIntervalIndex tree → Set Real)
    (hK : ∀ index, IsCompact (K index))
    (hKregular : ∀ index second, second ∈ K index →
      (fiber.first index, second) ∈
        actualA1VertexIntervalDifferentiabilitySource
          (fiber.fixed index) (fiber.site₁ index) (fiber.site₂ index)
          ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get
            index.1)
          index.2.toInterval)
    (j₀ : ActualA1BranchingIntervalIndex tree → Real)
    (hj₀ : ∀ index, 0 < j₀ index)
    (hjac : ∀ index second, second ∈ K index →
      j₀ index ≤
        |actualA1VertexIntervalVerticalJacobian
          (fiber.fixed index) (fiber.site₁ index) (fiber.site₂ index)
          ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get
            index.1)
          index.2.toInterval (fiber.first index, second)|) :
    ∃ certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
        OrdinaryGardenCoordinateCompactAtlas
          (actualA1BranchingOccurrenceFiberCoordinate tree fiber index),
      (∀ index, (certificate index).compactSet = K index) ∧
      (∀ index, (certificate index).jacLower = j₀ index) := by
  have hcertificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      ∃ certificate : OrdinaryGardenCoordinateCompactAtlas
          (actualA1BranchingOccurrenceFiberCoordinate tree fiber index),
        certificate.compactSet = K index ∧
          certificate.jacLower = j₀ index := by
    intro index
    change ∃ certificate : OrdinaryGardenCoordinateCompactAtlas
        (fun second => actualA1VertexIntervalPairMismatchChart
          (fiber.fixed index) (fiber.site₁ index) (fiber.site₂ index)
          ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get
            index.1)
          index.2.toInterval (fiber.first index, second)),
      certificate.compactSet = K index ∧
        certificate.jacLower = j₀ index
    exact exists_ordinaryGardenCoordinateCompactAtlas_of_actualA1Interval
      (fiber.fixed index) (fiber.sites_ne index)
      ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get
        index.1)
      index.2.toInterval (fiber.first index) (K index) (hK index)
      (hKregular index) (hj₀ index) (hjac index)
  choose certificate hcompact hjacobian using hcertificate
  exact ⟨certificate, hcompact, hjacobian⟩

/-- Final quantitative fixed-tree endpoint.  All compact atlases are derived
from the actual total-Jacobian lower bounds.  The probability is linear in
the threshold, up to the single displayed compact-exception mass, and the
finite branching count is explicitly order! times order squared. -/
theorem exists_measure_actualA1BranchingSmallDenominatorEvent_le_factorial_sq
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (K : ActualA1BranchingIntervalIndex tree → Set Real)
    (hK : ∀ index, IsCompact (K index))
    (hKregular : ∀ index second, second ∈ K index →
      (fiber.first index, second) ∈
        actualA1VertexIntervalDifferentiabilitySource
          (fiber.fixed index) (fiber.site₁ index) (fiber.site₂ index)
          ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get
            index.1)
          index.2.toInterval)
    (j₀ : ActualA1BranchingIntervalIndex tree → Real)
    (hj₀ : ∀ index, 0 < j₀ index)
    (hjac : ∀ index second, second ∈ K index →
      j₀ index ≤
        |actualA1VertexIntervalVerticalJacobian
          (fiber.fixed index) (fiber.site₁ index) (fiber.site₂ index)
          ((randomEigenmodeBinaryTreeA1VertexLinearExtensions tree).get
            index.1)
          index.2.toInterval (fiber.first index, second)|) :
    ∃ certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
        OrdinaryGardenCoordinateCompactAtlas
          (actualA1BranchingOccurrenceFiberCoordinate tree fiber index),
      (∀ index, (certificate index).compactSet = K index) ∧
      (∀ index, (certificate index).jacLower = j₀ index) ∧
      ∀ gamma : Real,
        massCoordinateLaw
            (actualA1BranchingSmallDenominatorEvent tree fiber gamma) ≤
          ((tree.shape.order.factorial *
              (tree.shape.order * tree.shape.order) : Nat) *
            actualA1BranchingCompactAtlasUniformBudget
              tree fiber certificate) *
              ENNReal.ofReal (2 * gamma) +
            massCoordinateLaw
              (actualA1BranchingOccurrenceCompactBadEvent tree K) := by
  obtain ⟨certificate, hcompact, hjacobian⟩ :=
    exists_actualA1BranchingOccurrenceCompactAtlasCertificates
      tree fiber K hK hKregular j₀ hj₀ hjac
  refine ⟨certificate, hcompact, hjacobian, ?_⟩
  intro gamma
  have hmeasure :=
    measure_actualA1BranchingSmallDenominatorEvent_le_compactAtlas
      tree fiber certificate gamma
  have hcoefficient :=
    actualA1BranchingCompactAtlasRegularCoefficient_le_factorial_sq
      tree fiber certificate
  have hbad :
      finiteCoordinateCompactAtlasBadEvent
          (actualA1BranchingOccurrenceFiberCoordinate tree fiber)
          certificate =
        actualA1BranchingOccurrenceCompactBadEvent tree K := by
    simp [finiteCoordinateCompactAtlasBadEvent,
      actualA1BranchingOccurrenceCompactBadEvent, hcompact]
  rw [hbad] at hmeasure
  exact hmeasure.trans (by
    gcongr)

end

end ArchonPhysics.PhyslibFPUTActualBranchingA1CompactSmallBall
