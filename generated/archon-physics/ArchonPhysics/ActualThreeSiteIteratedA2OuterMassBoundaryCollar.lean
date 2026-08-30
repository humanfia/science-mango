import ArchonPhysics.ActualThreeSiteIteratedA2OuterInverseMassStrip

/-!
# Quantitative support-boundary collars for the three-site outer channel

This module keeps the compactness cutoff independent of the inverse-mass
strip.  An inward cutoff of width `eta` removes at most `15 eta` of the iid
three-mass law.  The estimate is stated separately so that this boundary
mass is never hidden in the later inverse-function coefficient.
-/

namespace ArchonPhysics.ActualThreeSiteIteratedA2OuterMassBoundaryCollar

open ArchonPhysics
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The one-coordinate interval obtained by moving both support endpoints
inward by `eta`. -/
def threeSiteOuterInnerMassSupport (eta : Real) : Set Real :=
  Icc (massLower + eta) (massUpper - eta)

/-- The part of the physical one-coordinate support removed by the inward
cutoff. -/
def threeSiteOuterMassBoundaryCollar (eta : Real) : Set Real :=
  massSupport \ threeSiteOuterInnerMassSupport eta

theorem measurableSet_threeSiteOuterMassBoundaryCollar (eta : Real) :
    MeasurableSet (threeSiteOuterMassBoundaryCollar eta) := by
  exact measurableSet_Icc.diff measurableSet_Icc

/-- The first raw mass lies in the boundary collar. -/
def threeSiteOuterFirstMassBoundaryEvent (eta : Real) : Set MassTriple :=
  (threeSiteOuterMassBoundaryCollar eta ×ˢ Set.univ) ×ˢ Set.univ

/-- The middle raw mass lies in the boundary collar. -/
def threeSiteOuterMiddleMassBoundaryEvent (eta : Real) : Set MassTriple :=
  (Set.univ ×ˢ threeSiteOuterMassBoundaryCollar eta) ×ˢ Set.univ

/-- The third raw mass lies in the boundary collar. -/
def threeSiteOuterThirdMassBoundaryEvent (eta : Real) : Set MassTriple :=
  (Set.univ ×ˢ Set.univ) ×ˢ threeSiteOuterMassBoundaryCollar eta

/-- At least one of the three raw masses lies in the support-boundary
collar. -/
def threeSiteOuterMassBoundaryEvent (eta : Real) : Set MassTriple :=
  threeSiteOuterFirstMassBoundaryEvent eta ∪
    (threeSiteOuterMiddleMassBoundaryEvent eta ∪
      threeSiteOuterThirdMassBoundaryEvent eta)

theorem measurableSet_threeSiteOuterMassBoundaryEvent (eta : Real) :
    MeasurableSet (threeSiteOuterMassBoundaryEvent eta) := by
  exact
    ((((measurableSet_threeSiteOuterMassBoundaryCollar eta).prod
      MeasurableSet.univ).prod MeasurableSet.univ).union
        ((((MeasurableSet.univ.prod
          (measurableSet_threeSiteOuterMassBoundaryCollar eta)).prod
            MeasurableSet.univ).union
          ((MeasurableSet.univ.prod MeasurableSet.univ).prod
            (measurableSet_threeSiteOuterMassBoundaryCollar eta)))))

/-- A one-coordinate boundary collar has mass at most `5 eta`. -/
theorem massCoordinateLaw_threeSiteOuterMassBoundaryCollar_le
    {eta : Real} (_heta : 0 ≤ eta) :
    massCoordinateLaw (threeSiteOuterMassBoundaryCollar eta) ≤
      5 * ENNReal.ofReal eta := by
  let lowerCollar : Set Real := Icc massLower (massLower + eta)
  let upperCollar : Set Real := Icc (massUpper - eta) massUpper
  have hsubset : threeSiteOuterMassBoundaryCollar eta ⊆
      lowerCollar ∪ upperCollar := by
    intro mass hmass
    rcases hmass with ⟨hmassSupport, hmassInner⟩
    by_cases hlower : massLower + eta ≤ mass
    · have hupper : ¬ mass ≤ massUpper - eta := by
        intro hmassUpper
        exact hmassInner ⟨hlower, hmassUpper⟩
      exact Or.inr ⟨le_of_lt (lt_of_not_ge hupper), hmassSupport.2⟩
    · exact Or.inl
        ⟨hmassSupport.1, le_of_lt (lt_of_not_ge hlower)⟩
  have hlowerDensity := Measure.le_iff.mp
    massCoordinateLaw_le_fiveHalves_smul_volume
      lowerCollar measurableSet_Icc
  have hupperDensity := Measure.le_iff.mp
    massCoordinateLaw_le_fiveHalves_smul_volume
      upperCollar measurableSet_Icc
  have hlowerMeasure : massCoordinateLaw lowerCollar ≤
      (5 / 2 : ENNReal) * ENNReal.ofReal eta := by
    simpa [lowerCollar, Measure.smul_apply, Real.volume_Icc] using
      hlowerDensity
  have hupperLength : massUpper - (massUpper - eta) = eta := by ring
  have hupperMeasure : massCoordinateLaw upperCollar ≤
      (5 / 2 : ENNReal) * ENNReal.ofReal eta := by
    simpa [upperCollar, Measure.smul_apply, Real.volume_Icc,
      hupperLength] using hupperDensity
  calc
    massCoordinateLaw (threeSiteOuterMassBoundaryCollar eta) ≤
        massCoordinateLaw (lowerCollar ∪ upperCollar) :=
      measure_mono hsubset
    _ ≤ massCoordinateLaw lowerCollar + massCoordinateLaw upperCollar :=
      measure_union_le _ _
    _ ≤ (5 / 2 : ENNReal) * ENNReal.ofReal eta +
        (5 / 2 : ENNReal) * ENNReal.ofReal eta :=
      add_le_add hlowerMeasure hupperMeasure
    _ = 5 * ENNReal.ofReal eta := by
      rw [← add_mul]
      norm_num

theorem iidMassTripleLaw_firstMassBoundaryEvent_eq (eta : Real) :
    iidMassTripleLaw (threeSiteOuterFirstMassBoundaryEvent eta) =
      massCoordinateLaw (threeSiteOuterMassBoundaryCollar eta) := by
  simp [iidMassTripleLaw, iidMassPairLaw,
    threeSiteOuterFirstMassBoundaryEvent]

theorem iidMassTripleLaw_middleMassBoundaryEvent_eq (eta : Real) :
    iidMassTripleLaw (threeSiteOuterMiddleMassBoundaryEvent eta) =
      massCoordinateLaw (threeSiteOuterMassBoundaryCollar eta) := by
  simp [iidMassTripleLaw, iidMassPairLaw,
    threeSiteOuterMiddleMassBoundaryEvent]

theorem iidMassTripleLaw_thirdMassBoundaryEvent_eq (eta : Real) :
    iidMassTripleLaw (threeSiteOuterThirdMassBoundaryEvent eta) =
      massCoordinateLaw (threeSiteOuterMassBoundaryCollar eta) := by
  simp [iidMassTripleLaw, iidMassPairLaw,
    threeSiteOuterThirdMassBoundaryEvent]

/-- The complete iid three-mass boundary event has mass at most `15 eta`. -/
theorem iidMassTripleLaw_threeSiteOuterMassBoundaryEvent_le
    {eta : Real} (heta : 0 ≤ eta) :
    iidMassTripleLaw (threeSiteOuterMassBoundaryEvent eta) ≤
      15 * ENNReal.ofReal eta := by
  have hsingle :=
    massCoordinateLaw_threeSiteOuterMassBoundaryCollar_le heta
  calc
    iidMassTripleLaw (threeSiteOuterMassBoundaryEvent eta) ≤
        iidMassTripleLaw (threeSiteOuterFirstMassBoundaryEvent eta) +
          iidMassTripleLaw
            (threeSiteOuterMiddleMassBoundaryEvent eta ∪
              threeSiteOuterThirdMassBoundaryEvent eta) :=
      measure_union_le _ _
    _ ≤ iidMassTripleLaw (threeSiteOuterFirstMassBoundaryEvent eta) +
        (iidMassTripleLaw (threeSiteOuterMiddleMassBoundaryEvent eta) +
          iidMassTripleLaw (threeSiteOuterThirdMassBoundaryEvent eta)) :=
      add_le_add le_rfl (measure_union_le _ _)
    _ = massCoordinateLaw (threeSiteOuterMassBoundaryCollar eta) +
        (massCoordinateLaw (threeSiteOuterMassBoundaryCollar eta) +
          massCoordinateLaw (threeSiteOuterMassBoundaryCollar eta)) := by
      rw [iidMassTripleLaw_firstMassBoundaryEvent_eq,
        iidMassTripleLaw_middleMassBoundaryEvent_eq,
        iidMassTripleLaw_thirdMassBoundaryEvent_eq]
    _ ≤ 5 * ENNReal.ofReal eta +
        (5 * ENNReal.ofReal eta + 5 * ENNReal.ofReal eta) :=
      add_le_add hsingle (add_le_add hsingle hsingle)
    _ = 15 * ENNReal.ofReal eta := by ring

/-- The actual three-fold iid law is supported on the product support. -/
theorem iidMassTriple_mem_support_ae :
    ∀ᵐ triple ∂iidMassTripleLaw, triple ∈ iidMassTripleSupport := by
  have hpair : ∀ᵐ pair ∂iidMassPairLaw,
      pair ∈ iidMassPairSupport := by
    rw [iidMassPairLaw, Measure.ae_prod_mem_iff_ae_ae_mem]
    · filter_upwards [massCoordinate_mem_support_ae] with first hfirst
      filter_upwards [massCoordinate_mem_support_ae] with second hsecond
      exact ⟨hfirst, hsecond⟩
    · exact measurableSet_Icc.prod measurableSet_Icc
  rw [iidMassTripleLaw, Measure.ae_prod_mem_iff_ae_ae_mem]
  · filter_upwards [hpair] with pair hpair
    filter_upwards [massCoordinate_mem_support_ae] with third hthird
    exact ⟨hpair, hthird⟩
  · exact (measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Icc

end

end ArchonPhysics.ActualThreeSiteIteratedA2OuterMassBoundaryCollar
