import ArchonPhysics.ActualThreeSiteIteratedA2OuterExplicitDeterminantLower
import ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBall
import ArchonPhysics.QuantitativeJacobianGoodBadPushforward

/-!
# Global quantitative small balls for the three-site outer mismatch

The augmented outer chart retains the first and third raw masses.  On the
complement of the inverse-mass strip, its middle-mass derivative has one
fixed sign and an explicit lower bound.  Consequently the augmented chart
is globally injective on the whole regular set, so the area formula applies
once, without an existential finite atlas or an uncontrolled covering
cardinality.
-/

open scoped Matrix ENNReal

namespace ArchonPhysics.ActualThreeSiteIteratedA2OuterGlobalSmallBallRate

open ArchonPhysics
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.ActualThreeSiteIteratedA2OuterCompactAtlas
open ArchonPhysics.ActualThreeSiteIteratedA2OuterExplicitDeterminantLower
open ArchonPhysics.ActualThreeSiteIteratedA2OuterInverseMassStrip
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeBridges
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBall
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.QuantitativeJacobianGoodBadPushforward
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set

noncomputable section

private theorem threeSiteOuterFrequencyDerivative_second_nonpos
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeSiteOuterTripleHarmonic triple)) :
    massTripleLinearFunctional
        ((actualThreeMassFrequencyProjectorJacobianMatrix
          threeSiteOuterTripleBackground
          (0 : Lattice.Site 3) (1 : Lattice.Site 3)
          (2 : Lattice.Site 3) threeSiteOuterRepeatedSecondMode triple) 0)
        (massTripleBasis 1) ≤ 0 := by
  let dual := actualThreeMassDualHermitian threeSiteOuterTripleBackground
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) (2 : Lattice.Site 3) triple
  let direction := actualThreeMassCycleDirection
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) (2 : Lattice.Site 3) 1
  have hsimpleDual : SimpleOrderedSpectrum dual := by
    simpa [dual, threeSiteOuterTripleHarmonic] using
      simple_actualThreeMassDualHermitian_of_simple
        threeSiteOuterTripleBackground
        (0 : Lattice.Site 3) (1 : Lattice.Site 3)
        (2 : Lattice.Site 3) triple hsimple
  have hweight : 0 ≤ direction ⬝ᵥ
      (orderedModeProjector dual 1 *ᵥ direction) := by
    have hnonneg := orderedModeEnergy_nonneg dual 1 direction
    rw [orderedModeEnergy_eq_quadraticForm dual hsimpleDual] at hnonneg
    simpa [orderedModeProjectedState] using hnonneg
  have hfrequency : 0 < orderedModeFrequency
      (threeSiteOuterTripleHarmonic triple) 1 := by
    exact Real.sqrt_pos.2
      (threeSiteOuterTriple_secondEnergy_pos_of_simple triple hsimple)
  have hmass : 0 < triple.1.2 :=
    massLower_pos.trans_le (interior_subset htriple).1.2.1
  rw [massTripleLinearFunctional_massTripleBasis]
  change actualThreeMassFrequencyProjectorJacobianMatrix
      threeSiteOuterTripleBackground
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) (2 : Lattice.Site 3)
      threeSiteOuterRepeatedSecondMode triple 0 1 ≤ 0
  simp only [actualThreeMassFrequencyProjectorJacobianMatrix,
    scaledOrderedProjectorWeightMatrix, rowColumnScaledMatrix,
    actualThreeMassFrequencyRowScale, actualThreeMassRawMassColumnScale,
    orderedProjectorWeightMatrix]
  change (2 * orderedModeFrequency (threeSiteOuterTripleHarmonic triple) 1)⁻¹ *
      (direction ⬝ᵥ (orderedModeProjector dual 1 *ᵥ direction)) *
        -(triple.1.2 ^ 2)⁻¹ ≤ 0
  have hrow : 0 ≤
      (2 * orderedModeFrequency (threeSiteOuterTripleHarmonic triple) 1)⁻¹ := by
    positivity
  have hcolumn : -(triple.1.2 ^ 2)⁻¹ ≤ 0 :=
    neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg triple.1.2))
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hrow hweight) hcolumn

/-- The concrete outer mismatch increases strictly with the middle raw mass
at every interior point off the inverse-mass diagonal. -/
theorem threeSiteOuterTripleMismatchDerivative_second_pos
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hne : triple.1.1⁻¹ ≠ triple.2⁻¹) :
    0 < threeSiteOuterTripleMismatchDerivative triple (massTripleBasis 1) := by
  have hsimple := threeSiteOuterTripleHarmonic_simple_of_inverse_separated
    (interior_subset htriple) hne
  have hnonneg : 0 ≤ threeSiteOuterTripleMismatchDerivative triple
      (massTripleBasis 1) := by
    change 0 ≤ -massTripleLinearFunctional
      ((actualThreeMassFrequencyProjectorJacobianMatrix
        threeSiteOuterTripleBackground
        (0 : Lattice.Site 3) (1 : Lattice.Site 3)
        (2 : Lattice.Site 3) threeSiteOuterRepeatedSecondMode triple) 0)
      (massTripleBasis 1)
    exact neg_nonneg.mpr
      (threeSiteOuterFrequencyDerivative_second_nonpos htriple hsimple)
  have hneDerivative : threeSiteOuterTripleMismatchDerivative triple
      (massTripleBasis 1) ≠ 0 := by
    intro hzero
    exact hne
      (threeSiteOuterTripleMismatchDerivative_second_zero_forces_inverse_eq
        htriple hsimple hzero)
  exact hnonneg.lt_of_ne' hneDerivative


/-- The one-dimensional middle-mass fiber with the retained masses fixed. -/
def threeSiteOuterMiddleMassFiber (first third second : Real) : Real :=
  threeSiteOuterTripleMismatch ((first, second), third)

/-- Exact derivative of the middle-mass fiber at every interior regular
point. -/
theorem hasDerivAt_threeSiteOuterMiddleMassFiber
    {first second third : Real}
    (hfirst : first ∈ interior massSupport)
    (hsecond : second ∈ interior massSupport)
    (hthird : third ∈ interior massSupport)
    (hne : first⁻¹ ≠ third⁻¹) :
    HasDerivAt (threeSiteOuterMiddleMassFiber first third)
      (threeSiteOuterTripleMismatchDerivative ((first, second), third)
        (massTripleBasis 1)) second := by
  let triple : MassTriple := ((first, second), third)
  have htriple : triple ∈ interior iidMassTripleSupport := by
    simpa [triple, iidMassTripleSupport, iidMassPairSupport,
      interior_prod_eq] using
        (show (first ∈ interior massSupport ∧
          second ∈ interior massSupport) ∧
            third ∈ interior massSupport from ⟨⟨hfirst, hsecond⟩, hthird⟩)
  have hsimple := threeSiteOuterTripleHarmonic_simple_of_inverse_separated
    (interior_subset htriple) (by simpa [triple] using hne)
  let line : Real → MassTriple := fun value => ((first, value), third)
  have hline : HasDerivAt line (massTripleBasis 1) second := by
    simpa [line] using
      (((hasDerivAt_const second first).prodMk (hasDerivAt_id second)).prodMk
        (hasDerivAt_const second third))
  have hcomp :=
    (hasStrictFDerivAt_threeSiteOuterTripleMismatch htriple hsimple).hasFDerivAt.comp
      second hline.hasFDerivAt
  change HasDerivAt
    (fun value : Real => threeSiteOuterTripleMismatch ((first, value), third))
    (threeSiteOuterTripleMismatchDerivative ((first, second), third)
      (massTripleBasis 1)) second
  simpa [line, triple, Function.comp_def,
    ContinuousLinearMap.comp_apply] using hcomp.hasDerivAt

/-- For retained masses away from the inverse diagonal, the concrete
middle-mass fiber is strictly increasing on the entire closed physical mass
interval.  This is the global-injectivity bridge that replaces a finite
inverse-function atlas. -/
theorem strictMonoOn_threeSiteOuterMiddleMassFiber_massSupport
    {first third : Real}
    (hfirst : first ∈ interior massSupport)
    (hthird : third ∈ interior massSupport)
    (hne : first⁻¹ ≠ third⁻¹) :
    StrictMonoOn (threeSiteOuterMiddleMassFiber first third) massSupport := by
  rw [massSupport]
  apply strictMonoOn_of_hasDerivWithinAt_pos
    (convex_Icc massLower massUpper)
  · exact (continuous_threeSiteOuterTripleMismatch.comp
      (((continuous_const.prodMk continuous_id).prodMk
        continuous_const))).continuousOn
  · intro second hsecond
    have hsecondInterior : second ∈ interior massSupport := by
      simpa [massSupport] using hsecond
    exact (hasDerivAt_threeSiteOuterMiddleMassFiber
      hfirst hsecondInterior hthird hne).hasDerivWithinAt
  · intro second hsecond
    have hsecondInterior : second ∈ interior massSupport := by
      simpa [massSupport] using hsecond
    have htriple : ((first, second), third) ∈
        interior iidMassTripleSupport := by
      simpa [iidMassTripleSupport, iidMassPairSupport,
        interior_prod_eq] using
          (show (first ∈ interior massSupport ∧
            second ∈ interior massSupport) ∧
              third ∈ interior massSupport from
                ⟨⟨hfirst, hsecondInterior⟩, hthird⟩)
    exact threeSiteOuterTripleMismatchDerivative_second_pos htriple hne

/-- The global regular set: all three raw masses are interior and the first
and third inverse masses are separated by at least `delta`. -/
def threeSiteOuterGlobalGoodSet (delta : Real) : Set MassTriple :=
  interior iidMassTripleSupport ∩
    (threeSiteOuterInverseMassStrip delta)ᶜ

theorem measurableSet_threeSiteOuterGlobalGoodSet (delta : Real) :
    MeasurableSet (threeSiteOuterGlobalGoodSet delta) :=
  isOpen_interior.measurableSet.inter
    (measurableSet_threeSiteOuterInverseMassStrip delta).compl

theorem delta_le_inverse_separation_of_mem_globalGood
    {delta : Real} {triple : MassTriple}
    (htriple : triple ∈ threeSiteOuterGlobalGoodSet delta) :
    delta ≤ |triple.1.1⁻¹ - triple.2⁻¹| := by
  exact le_of_not_gt htriple.2

/-- Because the augmented chart retains the first and third masses, global
strict monotonicity in the middle mass makes it injective on the whole good
set, even though that set has two inverse-separation components. -/
theorem injOn_threeSiteOuterAugmentedChart_globalGood
    {delta : Real} (hdelta : 0 < delta) :
    InjOn threeSiteOuterAugmentedChart
      (threeSiteOuterGlobalGoodSet delta) := by
  intro first hfirst second hsecond heq
  have hfirstMass : first.1.1 = second.1.1 := by
    have h := congrArg (fun value : MassTriple => value.1.2) heq
    simpa [threeSiteOuterAugmentedChart] using h
  have hthirdMass : first.2 = second.2 := by
    have h := congrArg (fun value : MassTriple => value.2) heq
    simpa [threeSiteOuterAugmentedChart] using h
  have hmismatch : threeSiteOuterTripleMismatch first =
      threeSiteOuterTripleMismatch second := by
    have h := congrArg (fun value : MassTriple => value.1.1) heq
    simpa [threeSiteOuterAugmentedChart] using h
  have hfirstComponents :
      (first.1.1 ∈ interior massSupport ∧
        first.1.2 ∈ interior massSupport) ∧
          first.2 ∈ interior massSupport := by
    simpa [iidMassTripleSupport, iidMassPairSupport,
      interior_prod_eq] using hfirst.1
  have hsecondComponents :
      (second.1.1 ∈ interior massSupport ∧
        second.1.2 ∈ interior massSupport) ∧
          second.2 ∈ interior massSupport := by
    simpa [iidMassTripleSupport, iidMassPairSupport,
      interior_prod_eq] using hsecond.1
  have hmiddleFirst : first.1.2 ∈ massSupport :=
    interior_subset hfirstComponents.1.2
  have hmiddleSecond : second.1.2 ∈ massSupport :=
    interior_subset hsecondComponents.1.2
  have hseparated := delta_le_inverse_separation_of_mem_globalGood hfirst
  have hne : first.1.1⁻¹ ≠ first.2⁻¹ :=
    sub_ne_zero.mp (abs_pos.mp (hdelta.trans_le hseparated))
  have hmono := strictMonoOn_threeSiteOuterMiddleMassFiber_massSupport
    hfirstComponents.1.1 hfirstComponents.2 hne
  have hmiddle : first.1.2 = second.1.2 := by
    apply hmono.injOn hmiddleFirst hmiddleSecond
    change threeSiteOuterTripleMismatch
      ((first.1.1, first.1.2), first.2) =
        threeSiteOuterTripleMismatch
          ((second.1.1, second.1.2), second.2) at hmismatch
    rw [← hfirstMass, ← hthirdMass] at hmismatch
    exact hmismatch
  apply Prod.ext
  · exact Prod.ext hfirstMass hmiddle
  · exact hthirdMass

/-- The explicit determinant lower bound holds everywhere on the global
good set. -/
theorem abs_det_threeSiteOuterAugmentedDerivative_ge_on_globalGood
    {delta : Real} (hdelta : 0 < delta)
    {triple : MassTriple}
    (htriple : triple ∈ threeSiteOuterGlobalGoodSet delta) :
    delta ^ 2 / 4000 ≤
      |(threeSiteOuterAugmentedDerivative triple).det| := by
  exact abs_det_threeSiteOuterAugmentedDerivative_ge_delta_sq_div_fourThousand
    hdelta htriple.1
      (delta_le_inverse_separation_of_mem_globalGood htriple)


local instance tripleVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure MassTriple) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The endpoints of the uniform mass interval are null, so one mass lies
in the open support interval almost surely. -/
theorem massCoordinate_mem_interior_massSupport_ae_globalRate :
    ∀ᵐ mass ∂massCoordinateLaw, mass ∈ interior massSupport := by
  have hlower : massCoordinateLaw ({massLower} : Set Real) = 0 := by
    apply le_antisymm
    · exact (massCoordinateLaw_le_three_smul_volume
        ({massLower} : Set Real)).trans_eq (by simp)
    · exact bot_le
  have hupper : massCoordinateLaw ({massUpper} : Set Real) = 0 := by
    apply le_antisymm
    · exact (massCoordinateLaw_le_three_smul_volume
        ({massUpper} : Set Real)).trans_eq (by simp)
    · exact bot_le
  have hnotLower := measure_eq_zero_iff_ae_notMem.mp hlower
  have hnotUpper := measure_eq_zero_iff_ae_notMem.mp hupper
  filter_upwards [massCoordinate_mem_support_ae, hnotLower, hnotUpper]
    with mass hsupport hneLower hneUpper
  rw [massSupport, interior_Icc]
  simp only [mem_singleton_iff] at hneLower hneUpper
  exact ⟨lt_of_le_of_ne hsupport.1 (Ne.symm hneLower),
    lt_of_le_of_ne hsupport.2 hneUpper⟩

/-- The three-mass law lies in the open cube almost surely. -/
theorem iidMassTriple_mem_interior_support_ae_globalRate :
    ∀ᵐ triple ∂iidMassTripleLaw,
      triple ∈ interior iidMassTripleSupport := by
  have hpair : ∀ᵐ pair ∂iidMassPairLaw,
      pair ∈ interior iidMassPairSupport := by
    rw [iidMassPairLaw, Measure.ae_prod_mem_iff_ae_ae_mem]
    · filter_upwards [massCoordinate_mem_interior_massSupport_ae_globalRate]
        with first hfirst
      filter_upwards [massCoordinate_mem_interior_massSupport_ae_globalRate]
        with second hsecond
      simpa [iidMassPairSupport, interior_prod_eq] using
        (show first ∈ interior massSupport ∧
          second ∈ interior massSupport from ⟨hfirst, hsecond⟩)
    · exact isOpen_interior.measurableSet
  rw [iidMassTripleLaw, Measure.ae_prod_mem_iff_ae_ae_mem]
  · filter_upwards [hpair] with pair hpairInterior
    filter_upwards [massCoordinate_mem_interior_massSupport_ae_globalRate]
      with third hthird
    simpa [iidMassTripleSupport, interior_prod_eq] using
      (show pair ∈ interior iidMassPairSupport ∧
        third ∈ interior massSupport from ⟨hpairInterior, hthird⟩)
  · exact isOpen_interior.measurableSet

/-- The only positive-mass loss from the global good set is the explicit
inverse strip; support endpoints have zero iid mass. -/
theorem iidMassTripleLaw_globalGood_compl_le
    {delta : Real} (hdelta : 0 ≤ delta) :
    iidMassTripleLaw (threeSiteOuterGlobalGoodSet delta)ᶜ ≤
      10 * ENNReal.ofReal delta := by
  have hmono :
      iidMassTripleLaw (threeSiteOuterGlobalGoodSet delta)ᶜ ≤
        iidMassTripleLaw (threeSiteOuterInverseMassStrip delta) := by
    apply measure_mono_ae
    filter_upwards [iidMassTriple_mem_interior_support_ae_globalRate]
      with triple hinterior
    intro hbad
    by_cases hstrip : triple ∈ threeSiteOuterInverseMassStrip delta
    · exact hstrip
    · exact False.elim (hbad ⟨hinterior, hstrip⟩)
  exact hmono.trans
    (iidMassTripleLaw_threeSiteOuterInverseMassStrip_le hdelta)


/-- Fully explicit, atlas-free quantitative small-ball estimate.  The first
term is the explicit area-formula density upper-bound contribution and the
second is the inverse-mass strip loss. -/
theorem iidMassTripleLaw_threeSiteOuterNearMismatchEvent_le_explicitDet
    {delta epsilon : Real} (hdelta : 0 < delta) (hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
      (27 * (ENNReal.ofReal (delta ^ 2 / 4000))⁻¹) *
          (8 * ENNReal.ofReal epsilon) +
        10 * ENNReal.ofReal delta := by
  let good := threeSiteOuterGlobalGoodSet delta
  have hgood : MeasurableSet good := by
    simpa [good] using measurableSet_threeSiteOuterGlobalGoodSet delta
  have hderivative : ∀ triple ∈ good,
      HasFDerivWithinAt threeSiteOuterAugmentedChart
        (threeSiteOuterAugmentedDerivative triple) good triple := by
    intro triple htriple
    have hsep : delta ≤ |triple.1.1⁻¹ - triple.2⁻¹| := by
      exact delta_le_inverse_separation_of_mem_globalGood
        (by simpa [good] using htriple)
    have hne : triple.1.1⁻¹ ≠ triple.2⁻¹ :=
      sub_ne_zero.mp (abs_pos.mp (hdelta.trans_le hsep))
    have hsimple := threeSiteOuterTripleHarmonic_simple_of_inverse_separated
      (interior_subset (show triple ∈ interior iidMassTripleSupport from
        (by simpa [good] using htriple.1))) hne
    exact (hasStrictFDerivAt_threeSiteOuterAugmentedChart
      (by simpa [good] using htriple.1) hsimple).hasFDerivAt.hasFDerivWithinAt
  have hdetLower : 0 < delta ^ 2 / 4000 := by positivity
  have hsource : iidMassTripleLaw ≤
      (27 : ENNReal) • (volume : Measure MassTriple).restrict univ := by
    simpa using iidMassTripleLaw_le_twentySeven_smul_volume
  have hmap := map_apply_le_density_mul_add_complMass_of_good_patch
    (volume : Measure MassTriple) hgood (subset_univ good)
    threeSiteOuterAugmentedChart measurable_threeSiteOuterAugmentedChart
    threeSiteOuterAugmentedDerivative hderivative
    (by
      simpa [good] using
        (injOn_threeSiteOuterAugmentedChart_globalGood hdelta))
    hdetLower
    (fun triple htriple =>
      abs_det_threeSiteOuterAugmentedDerivative_ge_on_globalGood hdelta
        (by simpa [good] using htriple))
    iidMassTripleLaw 27 hsource
    (measurableSet_threeSiteOuterAugmentedSmallBallTarget epsilon)
  have heventSubset :
      iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
        iidMassTripleLaw
          (Set.preimage threeSiteOuterAugmentedChart
            (threeSiteOuterAugmentedSmallBallTarget epsilon)) := by
    apply measure_mono_ae
    filter_upwards [iidMassTriple_mem_interior_support_ae_globalRate]
      with triple hinterior
    intro hevent
    have hsupport := interior_subset hinterior
    rw [iidMassTripleSupport, iidMassPairSupport] at hsupport
    change ((threeSiteOuterTripleMismatch triple, triple.1.1), triple.2) ∈
      (Icc (-epsilon) epsilon ×ˢ Icc 0 2) ×ˢ Icc 0 2
    exact
      ⟨⟨abs_le.mp hevent,
          ⟨massLower_pos.le.trans hsupport.1.1.1,
            hsupport.1.1.2.trans (by norm_num [massUpper])⟩⟩,
        ⟨massLower_pos.le.trans hsupport.2.1,
          hsupport.2.2.trans (by norm_num [massUpper])⟩⟩
  calc
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
        iidMassTripleLaw
          (Set.preimage threeSiteOuterAugmentedChart
            (threeSiteOuterAugmentedSmallBallTarget epsilon)) := heventSubset
    _ = Measure.map threeSiteOuterAugmentedChart iidMassTripleLaw
          (threeSiteOuterAugmentedSmallBallTarget epsilon) := by
      rw [Measure.map_apply measurable_threeSiteOuterAugmentedChart
        (measurableSet_threeSiteOuterAugmentedSmallBallTarget epsilon)]
    _ ≤ (27 * (ENNReal.ofReal (delta ^ 2 / 4000))⁻¹) *
          (volume : Measure MassTriple)
            (threeSiteOuterAugmentedSmallBallTarget epsilon) +
        iidMassTripleLaw goodᶜ := hmap
    _ ≤ (27 * (ENNReal.ofReal (delta ^ 2 / 4000))⁻¹) *
          (8 * ENNReal.ofReal epsilon) +
        10 * ENNReal.ofReal delta := by
      rw [volume_threeSiteOuterAugmentedSmallBallTarget hepsilon]
      exact add_le_add le_rfl
        (by
          simpa [good] using
            (iidMassTripleLaw_globalGood_compl_le hdelta.le))


/-- The determinant-form estimate with its density coefficient normalized:
the regular contribution is exactly `864000 ε / δ²`. -/
theorem iidMassTripleLaw_threeSiteOuterNearMismatchEvent_le_explicit
    {delta epsilon : Real} (hdelta : 0 < delta) (hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
      10 * ENNReal.ofReal delta +
        864000 * ENNReal.ofReal epsilon * (ENNReal.ofReal delta)⁻¹ ^ 2 := by
  calc
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
        (27 * (ENNReal.ofReal (delta ^ 2 / 4000))⁻¹) *
            (8 * ENNReal.ofReal epsilon) +
          10 * ENNReal.ofReal delta :=
      iidMassTripleLaw_threeSiteOuterNearMismatchEvent_le_explicitDet
        hdelta hepsilon
    _ = 10 * ENNReal.ofReal delta +
        864000 * ENNReal.ofReal epsilon * (ENNReal.ofReal delta)⁻¹ ^ 2 := by
      rw [ENNReal.ofReal_div_of_pos
        (by norm_num : (0 : Real) < 4000)]
      rw [ENNReal.ofReal_pow hdelta.le]
      rw [ENNReal.ofReal_ofNat]
      rw [ENNReal.inv_div (Or.inl (by norm_num))
        (Or.inl (by norm_num))]
      rw [ENNReal.div_eq_inv_mul, ENNReal.inv_pow]
      ring


/-- Cubic reparameterization of the optimized estimate.  At mismatch window
`epsilon = rho³`, the explicit choice `delta = 60 rho` gives the Hölder
small-ball rate with constant `840`. -/
theorem iidMassTripleLaw_threeSiteOuterNearMismatchEvent_cube_le
    {rho : Real} (hrho : 0 < rho) :
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent (rho ^ 3)) ≤
      840 * ENNReal.ofReal rho := by
  calc
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent (rho ^ 3)) ≤
        10 * ENNReal.ofReal (60 * rho) +
          864000 * ENNReal.ofReal (rho ^ 3) *
            (ENNReal.ofReal (60 * rho))⁻¹ ^ 2 :=
      iidMassTripleLaw_threeSiteOuterNearMismatchEvent_le_explicit
        (mul_pos (by norm_num) hrho) (by positivity)
    _ = 840 * ENNReal.ofReal rho := by
      rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_pow]
      rw [ENNReal.toReal_ofReal (by positivity : (0 : Real) ≤ 60 * rho),
        ENNReal.toReal_ofReal (by positivity : (0 : Real) ≤ rho ^ 3),
        ENNReal.toReal_ofReal hrho.le]
      field_simp [ne_of_gt hrho]
      norm_num

end

end ArchonPhysics.ActualThreeSiteIteratedA2OuterGlobalSmallBallRate
