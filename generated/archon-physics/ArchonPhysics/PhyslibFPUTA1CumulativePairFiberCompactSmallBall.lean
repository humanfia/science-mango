import ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall

/-!
# Actual cumulative A1 pair-fiber transversality

An ordered higher-order denominator may be a cumulative sum of several local
A1 phase mismatches evaluated on the same retained mass coordinate.  This
module treats that sum as one actual scalar spectral chart.  Its vertical
derivative is the sum of the genuine per-term vertical Jacobians.  Local
invertibility therefore requires noncancellation of the total sum; separate
nonvanishing of the summands is neither required nor sufficient.

On an explicitly supplied compact set `K`, a positive lower bound

`j₀ ≤ |Σᵢ Jᵢ|`

gives a finite inverse-function atlas and the usual one-site small-ball bound
with density `5/2`.  No theorem below asserts that this lower bound holds on
the full mass support.

The final order-two adapter identifies the exact list
`[deltaOne, deltaTwo, deltaOne + deltaTwo]`: the first two coordinates use the
existing single-A1 compact certificates, while the third uses the cumulative
sum certificate proved here.  All three compact sets and Jacobian thresholds
remain independent displayed hypotheses.  This is deterministic frozen-mass
transversality, not re-Haar, high-order RPA, Markov closure, or recollision
decay.
-/

namespace ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall

open scoped BigOperators ENNReal

open ArchonPhysics
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberCompactSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Function MeasureTheory Set

noncomputable section

/-- Sum of a finite family of genuine actual A1 pair mismatch charts. -/
def physlibA1CumulativePairMismatchChart
    {Index : Type*} [DecidableEq Index]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Index → QuadraticPhaseTerm N) (active : Finset Index)
    (pair : Real × Real) : Real :=
  ∑ i ∈ active,
    physlibA1PairMismatchChart
      fixed site₁ site₂ observed (term i) pair

/-- Honest vertical Jacobian of the cumulative chart: the finite sum of the
actual per-term vertical Jacobians on the shared pair fiber. -/
def physlibA1CumulativePairMismatchVerticalJacobian
    {Index : Type*} [DecidableEq Index]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Index → QuadraticPhaseTerm N) (active : Finset Index)
    (pair : Real × Real) : Real :=
  ∑ i ∈ active,
    physlibA1PairMismatchVerticalJacobian
      fixed site₁ site₂ observed (term i) pair

/-- Common regularity source for every local mismatch appearing in the
cumulative sum.  The common physical interior is retained explicitly, also
for the empty family. -/
def physlibA1CumulativePairMismatchDifferentiabilitySource
    {Index : Type*} [DecidableEq Index]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Index → QuadraticPhaseTerm N) (active : Finset Index) :
    Set (Real × Real) :=
  {pair | pair ∈ interior iidMassPairSupport ∧
    ∀ i ∈ active,
      pair ∈ physlibA1PairMismatchDifferentiabilitySource
        fixed site₁ site₂ observed (term i)}

/-- The cumulative actual pair chart is measurable. -/
theorem measurable_physlibA1CumulativePairMismatchChart
    {Index : Type*} [DecidableEq Index]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Index → QuadraticPhaseTerm N) (active : Finset Index) :
    Measurable (physlibA1CumulativePairMismatchChart
      fixed site₁ site₂ observed term active) := by
  apply Finset.measurable_sum
  intro i _hi
  exact measurable_physlibA1PairMismatchChart
    fixed site₁ site₂ observed (term i)

/-- Strict derivative formula on the shared second-mass fiber.  Cancellation
is measured only after summing all actual vertical Jacobians. -/
theorem hasStrictDerivAt_physlibA1CumulativePairMismatchFiber
    {Index : Type*} [DecidableEq Index]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : Index → QuadraticPhaseTerm N) (active : Finset Index)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibA1CumulativePairMismatchDifferentiabilitySource
        fixed site₁ site₂ observed term active) :
    HasStrictDerivAt
      (fun second => physlibA1CumulativePairMismatchChart
        fixed site₁ site₂ observed term active (pair.1, second))
      (physlibA1CumulativePairMismatchVerticalJacobian
        fixed site₁ site₂ observed term active pair) pair.2 := by
  have hsum : HasStrictDerivAt
      (fun second => ∑ i ∈ active,
        physlibA1PairMismatchChart
          fixed site₁ site₂ observed (term i) (pair.1, second))
      (∑ i ∈ active,
        physlibA1PairMismatchVerticalJacobian
          fixed site₁ site₂ observed (term i) pair) pair.2 := by
    apply HasStrictDerivAt.fun_sum
    intro i hi
    exact hasStrictDerivAt_physlibA1PairMismatchFiber
      fixed hsite observed (term i) (hregular.2 i hi)
  simpa [physlibA1CumulativePairMismatchChart,
    physlibA1CumulativePairMismatchVerticalJacobian] using hsum

/-- Ordinary scalar derivative of the cumulative fiber is exactly the sum of
the actual vertical Jacobians. -/
theorem deriv_physlibA1CumulativePairMismatchFiber_eq_sum
    {Index : Type*} [DecidableEq Index]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : Index → QuadraticPhaseTerm N) (active : Finset Index)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibA1CumulativePairMismatchDifferentiabilitySource
        fixed site₁ site₂ observed term active) :
    deriv (fun second => physlibA1CumulativePairMismatchChart
        fixed site₁ site₂ observed term active (pair.1, second)) pair.2 =
      ∑ i ∈ active,
        physlibA1PairMismatchVerticalJacobian
          fixed site₁ site₂ observed (term i) pair := by
  exact (hasStrictDerivAt_physlibA1CumulativePairMismatchFiber
    fixed hsite observed term active hregular).hasDerivAt.deriv

/-- A noncritical total cumulative Jacobian gives an actual local open
injective patch.  Individual Jacobians may vanish or cancel away from the
base point. -/
theorem exists_physlibA1CumulativePairFiber_localInjectivePatch
    {Index : Type*} [DecidableEq Index]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : Index → QuadraticPhaseTerm N) (active : Finset Index)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibA1CumulativePairMismatchDifferentiabilitySource
        fixed site₁ site₂ observed term active)
    (hjac : physlibA1CumulativePairMismatchVerticalJacobian
      fixed site₁ site₂ observed term active pair ≠ 0) :
    ∃ patch : Set Real,
      pair.2 ∈ patch ∧ IsOpen patch ∧ MeasurableSet patch ∧
      patch ⊆ massSupport ∧
      InjOn
        (fun second => physlibA1CumulativePairMismatchChart
          fixed site₁ site₂ observed term active (pair.1, second)) patch := by
  let jacobian := physlibA1CumulativePairMismatchVerticalJacobian
    fixed site₁ site₂ observed term active pair
  let derivativeEquiv : Real ≃L[Real] Real :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 jacobian hjac)
  have hequiv : (derivativeEquiv : Real →L[Real] Real) =
      ContinuousLinearMap.toSpanSingleton Real jacobian := by
    apply ContinuousLinearMap.ext
    intro x
    simp [derivativeEquiv, jacobian, mul_comm]
  have hstrict := hasStrictDerivAt_physlibA1CumulativePairMismatchFiber
    fixed hsite observed term active hregular
  have hstrictEquiv : HasStrictFDerivAt
      (fun second => physlibA1CumulativePairMismatchChart
        fixed site₁ site₂ observed term active (pair.1, second))
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

/-- Compact actual cumulative fiber atlas under the honest noncancellation
bound on the total Jacobian sum. -/
theorem exists_atlasCard_physlibA1CumulativePairFiberCompact_smallBall
    {Index : Type*} [DecidableEq Index]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : Index → QuadraticPhaseTerm N) (active : Finset Index)
    (first : Real) (K : Set Real) (hK : IsCompact K)
    (hKregular : ∀ second ∈ K,
      (first, second) ∈
        physlibA1CumulativePairMismatchDifferentiabilitySource
          fixed site₁ site₂ observed term active)
    {j₀ : Real} (hj₀ : 0 < j₀)
    (hjac : ∀ second ∈ K, j₀ ≤
      |physlibA1CumulativePairMismatchVerticalJacobian
        fixed site₁ site₂ observed term active (first, second)|) :
    ∃ atlasCard : Nat,
      (∀ {target : Set Real}, MeasurableSet target →
        Measure.map
            (fun second => physlibA1CumulativePairMismatchChart
              fixed site₁ site₂ observed term active (first, second))
            (massCoordinateLaw.restrict K) target ≤
          ((atlasCard : ENNReal) *
            ((5 / 2 : ENNReal) * (ENNReal.ofReal j₀)⁻¹)) *
              (volume : Measure Real) target) ∧
      (∀ delta : Real,
        Measure.map
            (fun second => physlibA1CumulativePairMismatchChart
              fixed site₁ site₂ observed term active (first, second))
            massCoordinateLaw (Ioo (-delta) delta) ≤
          ((atlasCard : ENNReal) *
            ((5 / 2 : ENNReal) * (ENNReal.ofReal j₀)⁻¹)) *
              ENNReal.ofReal (2 * delta) + massCoordinateLaw Kᶜ) := by
  classical
  let chart : Real → Real := fun second =>
    physlibA1CumulativePairMismatchChart
      fixed site₁ site₂ observed term active (first, second)
  let derivative : Real → (Real →L[Real] Real) := fun second =>
    ContinuousLinearMap.toSpanSingleton Real
      (physlibA1CumulativePairMismatchVerticalJacobian
        fixed site₁ site₂ observed term active (first, second))
  have hchart : Measurable chart := by
    exact (measurable_physlibA1CumulativePairMismatchChart
      fixed site₁ site₂ observed term active).comp
        (measurable_const.prodMk measurable_id)
  have hlocal : ∀ point : K, ∃ patch : Set Real,
      IsOpen patch ∧ point.1 ∈ patch ∧ InjOn chart patch := by
    intro point
    have hregular := hKregular point.1 point.2
    have hnonzero : physlibA1CumulativePairMismatchVerticalJacobian
        fixed site₁ site₂ observed term active (first, point.1) ≠ 0 := by
      exact abs_pos.mp (hj₀.trans_le (hjac point.1 point.2))
    obtain ⟨patch, hpoint, hopen, _hmeasurable, _hsupport, hinjective⟩ :=
      exists_physlibA1CumulativePairFiber_localInjectivePatch
        fixed hsite observed term active hregular hnonzero
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
    have hstrict := hasStrictDerivAt_physlibA1CumulativePairMismatchFiber
      fixed hsite observed term active
        (hKregular second hsecond.1)
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
  refine ⟨atlas.card, ?_, ?_⟩
  · intro target htarget
    simpa [AtlasIndex, chart] using hmain.1 htarget
  · intro delta
    have hfull := hmain.2
      (target := Ioo (-delta) delta) measurableSet_Ioo
    rw [Real.volume_Ioo] at hfull
    convert hfull using 1 <;>
      simp [AtlasIndex, chart]
    rw [show delta + delta = delta * 2 by ring,
      ENNReal.ofReal_mul' (by norm_num : (0 : Real) ≤ 2)]
    norm_num [mul_assoc, mul_comm, mul_left_comm]

/-- The cumulative compact theorem constructs the same garden-coordinate
certificate interface as the single-A1 theorem. -/
theorem exists_ordinaryGardenCoordinateCompactAtlas_of_physlibA1Cumulative
    {Index : Type*} [DecidableEq Index]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : Index → QuadraticPhaseTerm N) (active : Finset Index)
    (first : Real) (K : Set Real) (hK : IsCompact K)
    (hKregular : ∀ second ∈ K,
      (first, second) ∈
        physlibA1CumulativePairMismatchDifferentiabilitySource
          fixed site₁ site₂ observed term active)
    {j₀ : Real} (hj₀ : 0 < j₀)
    (hjac : ∀ second ∈ K, j₀ ≤
      |physlibA1CumulativePairMismatchVerticalJacobian
        fixed site₁ site₂ observed term active (first, second)|) :
    ∃ certificate : OrdinaryGardenCoordinateCompactAtlas
        (fun second => physlibA1CumulativePairMismatchChart
          fixed site₁ site₂ observed term active (first, second)),
      certificate.compactSet = K ∧ certificate.jacLower = j₀ := by
  obtain ⟨atlasCard, hregular, _hfull⟩ :=
    exists_atlasCard_physlibA1CumulativePairFiberCompact_smallBall
      fixed hsite observed term active first K hK hKregular hj₀ hjac
  let chart : Real → Real := fun second =>
    physlibA1CumulativePairMismatchChart
      fixed site₁ site₂ observed term active (first, second)
  have hchart : Measurable chart :=
    (measurable_physlibA1CumulativePairMismatchChart
      fixed site₁ site₂ observed term active).comp
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

/-- Two local A1 terms viewed as a finite cumulative family. -/
def physlibA1OrderTwoTermFamily
    {N : Nat} [NeZero N]
    (termOne termTwo : QuadraticPhaseTerm N) :
    Fin 2 → QuadraticPhaseTerm N :=
  Fin.cases termOne (fun _ => termTwo)

@[simp] theorem physlibA1OrderTwoTermFamily_zero
    {N : Nat} [NeZero N]
    (termOne termTwo : QuadraticPhaseTerm N) :
    physlibA1OrderTwoTermFamily termOne termTwo 0 = termOne := rfl

@[simp] theorem physlibA1OrderTwoTermFamily_one
    {N : Nat} [NeZero N]
    (termOne termTwo : QuadraticPhaseTerm N) :
    physlibA1OrderTwoTermFamily termOne termTwo 1 = termTwo := rfl

/-- The cumulative chart of the order-two family is exactly the sum of the
two local mismatch charts. -/
theorem physlibA1OrderTwoCumulativePairMismatchChart_eq_add
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (termOne termTwo : QuadraticPhaseTerm N) (pair : Real × Real) :
    physlibA1CumulativePairMismatchChart
        fixed site₁ site₂ observed
          (physlibA1OrderTwoTermFamily termOne termTwo)
          Finset.univ pair =
      physlibA1PairMismatchChart
          fixed site₁ site₂ observed termOne pair +
        physlibA1PairMismatchChart
          fixed site₁ site₂ observed termTwo pair := by
  change (∑ i : Fin 2, physlibA1PairMismatchChart
    fixed site₁ site₂ observed
      (physlibA1OrderTwoTermFamily termOne termTwo i) pair) = _
  rw [Fin.sum_univ_two, physlibA1OrderTwoTermFamily_zero,
    physlibA1OrderTwoTermFamily_one]

/-- Exact first nontrivial ordered-history adapter.  The third denominator
is the new cumulative actual chart, not another postulated A1 term. -/
theorem physlibA1OrderTwoDenominators_eq_local_local_cumulative
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (termOne termTwo : QuadraticPhaseTerm N) (pair : Real × Real) :
    orderedHistoryDenominators
        [physlibA1PairMismatchChart
          fixed site₁ site₂ observed termOne pair,
         physlibA1PairMismatchChart
          fixed site₁ site₂ observed termTwo pair] =
      [physlibA1PairMismatchChart
          fixed site₁ site₂ observed termOne pair,
       physlibA1PairMismatchChart
          fixed site₁ site₂ observed termTwo pair,
       physlibA1CumulativePairMismatchChart
          fixed site₁ site₂ observed
            (physlibA1OrderTwoTermFamily termOne termTwo)
            Finset.univ pair] := by
  rw [orderedHistoryDenominators_two_eq_local_and_cumulative,
    physlibA1OrderTwoCumulativePairMismatchChart_eq_add]

/-- Three honest compact certificates for the order-two list.  The two local
coordinates use the existing single-A1 theorem; the cumulative coordinate
uses the total-Jacobian theorem above.  No threshold is globalized. -/
theorem exists_physlibA1OrderTwoCompactAtlasCertificates
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (termOne termTwo : QuadraticPhaseTerm N) (first : Real)
    (KOne KTwo KSum : Set Real)
    (hKOne : IsCompact KOne) (hKTwo : IsCompact KTwo)
    (hKSum : IsCompact KSum)
    (hregularOne : ∀ second ∈ KOne,
      (first, second) ∈ physlibA1PairMismatchDifferentiabilitySource
        fixed site₁ site₂ observed termOne)
    (hregularTwo : ∀ second ∈ KTwo,
      (first, second) ∈ physlibA1PairMismatchDifferentiabilitySource
        fixed site₁ site₂ observed termTwo)
    (hregularSum : ∀ second ∈ KSum,
      (first, second) ∈
        physlibA1CumulativePairMismatchDifferentiabilitySource
          fixed site₁ site₂ observed
            (physlibA1OrderTwoTermFamily termOne termTwo) Finset.univ)
    {jOne jTwo jSum : Real}
    (hjOne : 0 < jOne) (hjTwo : 0 < jTwo) (hjSum : 0 < jSum)
    (hjacOne : ∀ second ∈ KOne, jOne ≤
      |physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed termOne (first, second)|)
    (hjacTwo : ∀ second ∈ KTwo, jTwo ≤
      |physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed termTwo (first, second)|)
    (hjacSum : ∀ second ∈ KSum, jSum ≤
      |physlibA1CumulativePairMismatchVerticalJacobian
        fixed site₁ site₂ observed
          (physlibA1OrderTwoTermFamily termOne termTwo)
          Finset.univ (first, second)|) :
    (∃ certificate : OrdinaryGardenCoordinateCompactAtlas
        (fun second => physlibA1PairMismatchChart
          fixed site₁ site₂ observed termOne (first, second)),
      certificate.compactSet = KOne ∧ certificate.jacLower = jOne) ∧
    (∃ certificate : OrdinaryGardenCoordinateCompactAtlas
        (fun second => physlibA1PairMismatchChart
          fixed site₁ site₂ observed termTwo (first, second)),
      certificate.compactSet = KTwo ∧ certificate.jacLower = jTwo) ∧
    (∃ certificate : OrdinaryGardenCoordinateCompactAtlas
        (fun second => physlibA1CumulativePairMismatchChart
          fixed site₁ site₂ observed
            (physlibA1OrderTwoTermFamily termOne termTwo)
            Finset.univ (first, second)),
      certificate.compactSet = KSum ∧ certificate.jacLower = jSum) := by
  exact ⟨exists_ordinaryGardenCoordinateCompactAtlas_of_physlibA1
      fixed hsite observed termOne first KOne hKOne
        hregularOne hjOne hjacOne,
    exists_ordinaryGardenCoordinateCompactAtlas_of_physlibA1
      fixed hsite observed termTwo first KTwo hKTwo
        hregularTwo hjTwo hjacTwo,
    exists_ordinaryGardenCoordinateCompactAtlas_of_physlibA1Cumulative
      fixed hsite observed
        (physlibA1OrderTwoTermFamily termOne termTwo) Finset.univ
        first KSum hKSum hregularSum hjSum hjacSum⟩

end

end ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall
