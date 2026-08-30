import ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyCubeRateGardenSchedule
import ArchonPhysics.FreeFPUTObservedChildAcousticMomentExplicitBound

/-!
# Inner gaps and nested bad events for the three-site ordinary outer family

For each of the four displayed ordinary outer histories, the inner quadratic
phase is

`omega₂ - omega₁ - omega₂ = -omega₁`.

The coordinate branch only changes its sign.  Consequently the absolute
inner mismatch is exactly the first positive ordered frequency.  On the
clipped three-mass family this frequency has the deterministic lower bound
`1 / 15`; no spectral-averaging hypothesis is needed for the inner event.

We then form the union of the already controlled outer event and this inner
event.  This is a bad event for the two separately displayed nested gaps.  It
does not assert control of the `total` mismatch channel or a microscopic RPA
closure.
-/

namespace ArchonPhysics
namespace ActualThreeSiteIteratedA2OrdinaryOuterFamilyNestedSmallBall

open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeSiteIteratedA2CubeRateGardenSchedule
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyCubeRateGardenSchedule
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBall
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeBridges
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTObservedChildAcousticMomentExplicitBound
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
open ArchonPhysics.CanonicalCollisionSoftLegBound
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-! ## Exact inner mismatch -/

/-- Before the coordinate-branch sign is applied, every displayed history
has the same inner quadratic phase `-omega₁`. -/
theorem threeSiteOrdinaryOuterHistory_innerQuadraticPhaseMismatch_eq
    (m : Lattice.PositiveMassConfig 3)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    quadraticPhaseMismatch (modeFrequency m)
        (iteratedQuadraticFirstPicardMode
          (threeSiteOrdinaryOuterHistoryTerm index))
        (iteratedQuadraticInnerEntry
          (threeSiteOrdinaryOuterHistoryTerm index)).1 =
      -modeFrequency m firstPositivePhysicalModeThree := by
  rcases index with ⟨slot, branch⟩
  fin_cases slot <;> fin_cases branch <;>
    simp [quadraticPhaseMismatch_eq_output_sub_chargeFrequency,
      chargeFrequency_quadraticPhaseCharge,
      threeSiteOrdinaryOuterHistoryTerm, threeSiteOrdinaryOuterModes,
      iteratedQuadraticFirstPicardMode, iteratedQuadraticOuterModes,
      iteratedQuadraticFirstPicardSlot, iteratedQuadraticInnerEntry]

/-- The full inner mismatch has the same branch coefficient as the outer
mismatch, multiplying the first rather than the second positive frequency. -/
theorem threeSiteOrdinaryOuterHistory_innerMismatch_eq
    (m : Lattice.PositiveMassConfig 3)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    iteratedQuadraticInnerMismatch m
        (threeSiteOrdinaryOuterHistoryTerm index) =
      threeSiteOuterHistoryMismatchSign
          (threeSiteOrdinaryOuterHistoryTerm index) *
        modeFrequency m firstPositivePhysicalModeThree := by
  unfold iteratedQuadraticInnerMismatch
    firstPicardCoordinateBranchMismatch
  rw [threeSiteOrdinaryOuterHistory_innerQuadraticPhaseMismatch_eq]
  unfold threeSiteOuterHistoryMismatchSign
  ring

/-- The actual inner mismatch in the three raw-mass coordinates. -/
def threeSiteOrdinaryOuterHistoryTripleInnerMismatch
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (triple : MassTriple) : Real :=
  iteratedQuadraticInnerMismatch
    (threeSiteOuterTripleMassConfig triple)
    (threeSiteOrdinaryOuterHistoryTerm index)

/-- The common absolute inner gap, written in ordered spectral coordinates. -/
def threeSiteFirstPositiveFrequencyGap (triple : MassTriple) : Real :=
  orderedModeFrequency (threeSiteOuterTripleHarmonic triple) 0

theorem threeSiteFirstPositiveFrequencyGap_eq_modeFrequency
    (triple : MassTriple) :
    threeSiteFirstPositiveFrequencyGap triple =
      modeFrequency (threeSiteOuterTripleMassConfig triple)
        firstPositivePhysicalModeThree := by
  change orderedModeFrequency
      (harmonicHermitian (threeSiteOuterTripleMassConfig triple)) 0 =
    modeFrequency (threeSiteOuterTripleMassConfig triple)
      firstPositivePhysicalModeThree
  rw [orderedModeFrequency_harmonicHermitian_eq]
  rfl

/-- Taking absolute value removes the branch sign for all four histories. -/
theorem abs_threeSiteOrdinaryOuterHistoryTripleInnerMismatch_eq
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (triple : MassTriple) :
    |threeSiteOrdinaryOuterHistoryTripleInnerMismatch index triple| =
      threeSiteFirstPositiveFrequencyGap triple := by
  rw [threeSiteOrdinaryOuterHistoryTripleInnerMismatch,
    threeSiteOrdinaryOuterHistory_innerMismatch_eq, abs_mul]
  have hsign :
      |threeSiteOuterHistoryMismatchSign
        (threeSiteOrdinaryOuterHistoryTerm index)| = 1 := by
    rcases threeSiteOuterHistoryMismatchSign_eq_neg_one_or_one
        (threeSiteOrdinaryOuterHistoryTerm index) with hnegative | hpositive
    · rw [hnegative]
      norm_num
    · rw [hpositive]
      norm_num
  rw [hsign, one_mul,
    abs_of_nonneg (modeFrequency_nonneg
      (threeSiteOuterTripleMassConfig triple)
      firstPositivePhysicalModeThree)]
  exact (threeSiteFirstPositiveFrequencyGap_eq_modeFrequency triple).symm

theorem continuous_threeSiteFirstPositiveFrequencyGap :
    Continuous threeSiteFirstPositiveFrequencyGap := by
  exact (continuous_orderedModeFrequency (iota := Lattice.Site 3) (0 : Fin 3)).comp
    (continuous_threeMassHarmonicHermitian threeSiteOuterTripleBackground
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) (2 : Lattice.Site 3))

/-- Positivity is unconditional: ordered index zero is not the deterministic
translation mode. -/
theorem threeSiteFirstPositiveFrequencyGap_pos (triple : MassTriple) :
    0 < threeSiteFirstPositiveFrequencyGap triple := by
  change 0 < orderedModeFrequency
    (harmonicHermitian (threeSiteOuterTripleMassConfig triple)) 0
  exact (orderedModeFrequency_pos_iff_ne_last_unconditional
    (threeSiteOuterTripleMassConfig triple) 0).2 (by decide)

/-- A coarse but explicit uniform floor.  Clipping puts every mass below `2`,
and the finite-volume acoustic estimate at `N = 3` gives
`omega₁² >= 1 / 216 > (1 / 15)²`. -/
theorem one_div_fifteen_lt_threeSiteFirstPositiveFrequencyGap
    (triple : MassTriple) :
    (1 / 15 : Real) < threeSiteFirstPositiveFrequencyGap triple := by
  let m := threeSiteOuterTripleMassConfig triple
  have hclip (x : Real) : clippedMass x ≤ 2 :=
    (clippedMass_mem_support x).2.trans (by norm_num [massUpper])
  have hmassUpper : ∀ site, m.mass site ≤ 2 := by
    intro site
    fin_cases site <;>
      simp [m, threeSiteOuterTripleMassConfig, threeMassSiteConfig]
      <;> exact hclip _
  have hfrequency :
      0 < modeFrequency m firstPositivePhysicalModeThree := by
    have hpositive := threeSiteFirstPositiveFrequencyGap_pos triple
    rw [threeSiteFirstPositiveFrequencyGap_eq_modeFrequency] at hpositive
    simpa [m] using hpositive
  have hlower := modeFrequencySq_ge_explicit_of_pos
    m 2 (by norm_num) hmassUpper firstPositivePhysicalModeThree hfrequency
  rw [← modeFrequency_sq] at hlower
  have hgap :
      modeFrequency m firstPositivePhysicalModeThree =
        threeSiteFirstPositiveFrequencyGap triple := by
    exact (threeSiteFirstPositiveFrequencyGap_eq_modeFrequency triple).symm
  rw [hgap] at hlower
  norm_num at hlower
  have hgapNonneg : 0 ≤ threeSiteFirstPositiveFrequencyGap triple :=
    (threeSiteFirstPositiveFrequencyGap_pos triple).le
  nlinarith

/-! ## Measurable inner near-events and their probability -/

def threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (epsilon : Real) : Set MassTriple :=
  {triple |
    |threeSiteOrdinaryOuterHistoryTripleInnerMismatch index triple| ≤ epsilon}

theorem threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent_eq
    (index : ThreeSiteOrdinaryOuterHistoryIndex) (epsilon : Real) :
    threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent index epsilon =
      {triple | threeSiteFirstPositiveFrequencyGap triple ≤ epsilon} := by
  ext triple
  change |threeSiteOrdinaryOuterHistoryTripleInnerMismatch index triple| ≤
      epsilon ↔ threeSiteFirstPositiveFrequencyGap triple ≤ epsilon
  rw [abs_threeSiteOrdinaryOuterHistoryTripleInnerMismatch_eq]

theorem measurableSet_threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent
    (index : ThreeSiteOrdinaryOuterHistoryIndex) (epsilon : Real) :
    MeasurableSet
      (threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent index epsilon) := by
  rw [threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent_eq]
  exact measurableSet_le
    continuous_threeSiteFirstPositiveFrequencyGap.measurable measurable_const

theorem threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent_eq_empty
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    {epsilon : Real} (hepsilon : epsilon < 1 / 15) :
    threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent index epsilon = ∅ := by
  rw [threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent_eq]
  ext triple
  change threeSiteFirstPositiveFrequencyGap triple ≤ epsilon ↔ False
  constructor
  · intro htriple
    exact (not_le_of_gt
      (one_div_fifteen_lt_threeSiteFirstPositiveFrequencyGap triple))
        (htriple.trans (le_of_lt hepsilon))
  · intro hfalse
    exact hfalse.elim

/-- A global all-width linear bound.  Below `1/15` the event is empty; above
that floor the total probability bound `1` is enough. -/
theorem iidMassTripleLaw_threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent_le
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    {epsilon : Real} (_hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent index epsilon) ≤
      15 * ENNReal.ofReal epsilon := by
  by_cases hsmall : epsilon < 1 / 15
  · rw [threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent_eq_empty
      index hsmall]
    simp
  · have honeReal : (1 : Real) ≤ 15 * epsilon := by
      nlinarith
    calc
      iidMassTripleLaw
          (threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent index epsilon) ≤
          iidMassTripleLaw Set.univ := measure_mono (subset_univ _)
      _ = 1 := by
        simp [iidMassTripleLaw,
          ArchonPhysics.TwoParameterSpectralAveragingAtlas.iidMassPairLaw]
      _ = ENNReal.ofReal 1 := by norm_num
      _ ≤ ENNReal.ofReal (15 * epsilon) :=
        ENNReal.ofReal_le_ofReal honeReal
      _ = 15 * ENNReal.ofReal epsilon := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 15)]
        norm_num

theorem iidMassTripleLaw_threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent_zero
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    iidMassTripleLaw
      (threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent index 0) = 0 := by
  rw [threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent_eq_empty index
    (by norm_num : (0 : Real) < 1 / 15)]
  simp

/-- Union over all four displayed inner histories. -/
def threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent
    (epsilon : Real) : Set MassTriple :=
  ⋃ index : ThreeSiteOrdinaryOuterHistoryIndex,
    threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent index epsilon

/-- All four absolute inner events are identical, so the family union loses
no factor of four. -/
theorem threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_eq
    (epsilon : Real) :
    threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent epsilon =
      {triple | threeSiteFirstPositiveFrequencyGap triple ≤ epsilon} := by
  apply le_antisymm
  · intro triple htriple
    obtain ⟨index, hindex⟩ := mem_iUnion.mp htriple
    rw [threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent_eq] at hindex
    exact hindex
  · intro triple htriple
    apply mem_iUnion.mpr
    refine ⟨((0, 0) : ThreeSiteOrdinaryOuterHistoryIndex), ?_⟩
    rw [threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent_eq]
    exact htriple

theorem measurableSet_threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent
    (epsilon : Real) :
    MeasurableSet
      (threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent epsilon) := by
  rw [threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_eq]
  exact measurableSet_le
    continuous_threeSiteFirstPositiveFrequencyGap.measurable measurable_const

theorem threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_eq_empty
    {epsilon : Real} (hepsilon : epsilon < 1 / 15) :
    threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent epsilon = ∅ := by
  rw [threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_eq]
  ext triple
  change threeSiteFirstPositiveFrequencyGap triple ≤ epsilon ↔ False
  constructor
  · intro htriple
    exact (not_le_of_gt
      (one_div_fifteen_lt_threeSiteFirstPositiveFrequencyGap triple))
        (htriple.trans (le_of_lt hepsilon))
  · intro hfalse
    exact hfalse.elim

theorem
    iidMassTripleLaw_threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_le
    {epsilon : Real} (_hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent epsilon) ≤
      15 * ENNReal.ofReal epsilon := by
  rw [threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_eq]
  simpa [threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent_eq] using
    iidMassTripleLaw_threeSiteOrdinaryOuterHistoryInnerNearMismatchEvent_le
      ((0, 0) : ThreeSiteOrdinaryOuterHistoryIndex) _hepsilon

theorem
    iidMassTripleLaw_threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_zero :
    iidMassTripleLaw
      (threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent 0) = 0 := by
  rw [threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_eq_empty
    (by norm_num : (0 : Real) < 1 / 15)]
  simp

/-! ## Outer/inner nested bad event -/

/-- Union of the separately small outer and inner gaps.  This definition does
not include the `total` mismatch channel. -/
def threeSiteOrdinaryOuterHistoryNestedBadEvent
    (outerEpsilon innerEpsilon : Real) : Set MassTriple :=
  threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent outerEpsilon ∪
    threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent innerEpsilon

theorem measurableSet_threeSiteOrdinaryOuterHistoryNestedBadEvent
    (outerEpsilon innerEpsilon : Real) :
    MeasurableSet
      (threeSiteOrdinaryOuterHistoryNestedBadEvent
        outerEpsilon innerEpsilon) :=
  (measurableSet_threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
      outerEpsilon).union
    (measurableSet_threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent
      innerEpsilon)

theorem iidMassTripleLaw_threeSiteOrdinaryOuterHistoryNestedBadEvent_le
    {outerEpsilon innerEpsilon : Real}
    (houter : 0 ≤ outerEpsilon) (hinner : 0 ≤ innerEpsilon) :
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryNestedBadEvent
          outerEpsilon innerEpsilon) ≤
      840 * ENNReal.ofReal (outerEpsilon ^ ((3 : Real)⁻¹)) +
        15 * ENNReal.ofReal innerEpsilon := by
  calc
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryNestedBadEvent
          outerEpsilon innerEpsilon) ≤
      iidMassTripleLaw
          (threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent outerEpsilon) +
        iidMassTripleLaw
          (threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent
            innerEpsilon) := by
        exact measure_union_le _ _
    _ ≤ 840 * ENNReal.ofReal (outerEpsilon ^ ((3 : Real)⁻¹)) +
        15 * ENNReal.ofReal innerEpsilon :=
      add_le_add
        (iidMassTripleLaw_threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_le
          houter)
        (iidMassTripleLaw_threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_le
          hinner)

/-- Below the deterministic inner floor, the nested bad event is exactly the
outer family event. -/
theorem threeSiteOrdinaryOuterHistoryNestedBadEvent_eq_outer
    (outerEpsilon : Real) {innerEpsilon : Real}
    (hinner : innerEpsilon < 1 / 15) :
    threeSiteOrdinaryOuterHistoryNestedBadEvent
        outerEpsilon innerEpsilon =
      threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent outerEpsilon := by
  unfold threeSiteOrdinaryOuterHistoryNestedBadEvent
  rw [threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_eq_empty hinner]
  exact union_empty _

/-- Equal sextic cutoffs for the two separately displayed nested gaps. -/
def threeSiteOrdinaryOuterHistoryNestedSexticBadEvent
    (g : Real) : Set MassTriple :=
  threeSiteOrdinaryOuterHistoryNestedBadEvent
    (sexticCouplingCutoff g) (sexticCouplingCutoff g)

/-- Globally available bound.  The inner term is of order `|g|^6`; the outer
term is the proved cube-rate `|g|^2` contribution. -/
theorem iidMassTripleLaw_threeSiteOrdinaryOuterHistoryNestedSexticBadEvent_le
    (g : Real) :
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryNestedSexticBadEvent g) ≤
      840 * ENNReal.ofReal (squareCouplingCutoff g) +
        15 * ENNReal.ofReal (sexticCouplingCutoff g) := by
  have houter :
      iidMassTripleLaw
          (threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
            (sexticCouplingCutoff g)) ≤
        840 * ENNReal.ofReal (squareCouplingCutoff g) := by
    simpa [ordinaryOuterFamilySexticCutoffBadBudgetENNReal] using
      ordinaryOuterFamilySexticCutoffBadBudgetENNReal_le g
  have hinner :=
    iidMassTripleLaw_threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent_le
      (show 0 ≤ sexticCouplingCutoff g by
        unfold sexticCouplingCutoff
        positivity)
  calc
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryNestedSexticBadEvent g) ≤
      iidMassTripleLaw
          (threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
            (sexticCouplingCutoff g)) +
        iidMassTripleLaw
          (threeSiteOrdinaryOuterHistoryFamilyInnerNearMismatchEvent
            (sexticCouplingCutoff g)) := by
        exact measure_union_le _ _
    _ ≤ 840 * ENNReal.ofReal (squareCouplingCutoff g) +
        15 * ENNReal.ofReal (sexticCouplingCutoff g) :=
      add_le_add houter hinner

theorem threeSiteOrdinaryOuterHistoryNestedSexticBadEvent_eq_outer
    {g : Real} (hcutoff : sexticCouplingCutoff g < 1 / 15) :
    threeSiteOrdinaryOuterHistoryNestedSexticBadEvent g =
      threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
        (sexticCouplingCutoff g) :=
  threeSiteOrdinaryOuterHistoryNestedBadEvent_eq_outer
    (sexticCouplingCutoff g) hcutoff

/-- In the perturbative range where the sextic cutoff lies below the fixed
inner floor, the complete outer/inner bad event retains the sharp displayed
outer-family bound. -/
theorem iidMassTripleLaw_threeSiteOrdinaryOuterHistoryNestedSexticBadEvent_le_sharp
    {g : Real} (hcutoff : sexticCouplingCutoff g < 1 / 15) :
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryNestedSexticBadEvent g) ≤
      840 * ENNReal.ofReal (squareCouplingCutoff g) := by
  rw [threeSiteOrdinaryOuterHistoryNestedSexticBadEvent_eq_outer hcutoff]
  simpa [ordinaryOuterFamilySexticCutoffBadBudgetENNReal] using
    ordinaryOuterFamilySexticCutoffBadBudgetENNReal_le g

end


end ActualThreeSiteIteratedA2OrdinaryOuterFamilyNestedSmallBall
end ArchonPhysics
