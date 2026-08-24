import FamilyStickyCinematicL32FiniteIncidenceNormCriticalBallV1
import FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
import FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1

open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteIncidenceNormCriticalBallV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1

noncomputable section

/-!
# The measurable global norm-cover cell `E_B`

After one global dyadic norm scale has been fixed, the canonical pointwise
norm centre is coded by the maximal fixed-scale cover of the ambient finite
family.  This code is a function of the literal active incidence pattern, so
its cells are measurable.  Finite measure pigeonholing selects one `E_B`, and
the local-to-global localization theorem proves `B_x ⊆ F_x ∩ 3B` on that
cell without a retention callback.
-/

universe u v w

variable {X : Type u} {index : Type v} {alpha : Type w}
  [MeasurableSpace X] [DecidableEq alpha]


/-- Global-cover label of one active pattern. -/
noncomputable def finiteIncidenceNormGlobalCoverLabelValue
    (ambientFamily : Finset alpha) (fallback : FiniteMetricMember ambientFamily)
    (familyOfActive : Finset index → Finset alpha)
    (distance : alpha → alpha → Real)
    (delta ceiling exponent globalScale : Real)
    (hsymm : ∀ f g, distance f g = distance g f)
    (active : Finset index) : alpha := by
  classical
  exact if hfamily : (familyOfActive active).Nonempty then
    let center := finiteCriticalMaximizerCenter (familyOfActive active)
      distance delta ceiling exponent hfamily
    if hcenter : center ∈ ambientFamily then
      finiteMetricCoverCode ambientFamily distance globalScale hsymm
        ⟨center, hcenter⟩
    else
      finiteMetricCoverCode ambientFamily distance globalScale hsymm fallback
  else
    finiteMetricCoverCode ambientFamily distance globalScale hsymm fallback

/-- Pointwise global-cover label read from the finite incidence pattern. -/
noncomputable def finiteIncidenceNormGlobalCoverLabel
    (ambient : Finset index) (incidence : index → X → Prop)
    (ambientFamily : Finset alpha) (fallback : FiniteMetricMember ambientFamily)
    (familyOfActive : Finset index → Finset alpha)
    (distance : alpha → alpha → Real)
    (delta ceiling exponent globalScale : Real)
    (hsymm : ∀ f g, distance f g = distance g f) : X → alpha :=
  fun x => finiteIncidenceNormGlobalCoverLabelValue ambientFamily fallback
    familyOfActive distance delta ceiling exponent globalScale hsymm
    (finiteIncidenceActiveAtPoint ambient incidence x)

/-- The global cover label is measurable solely from measurable incidence
events. -/
theorem measurable_finiteIncidenceNormGlobalCoverLabel
    [MeasurableSpace alpha]
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (ambientFamily : Finset alpha) (fallback : FiniteMetricMember ambientFamily)
    (familyOfActive : Finset index → Finset alpha)
    (distance : alpha → alpha → Real)
    (delta ceiling exponent globalScale : Real)
    (hsymm : ∀ f g, distance f g = distance g f) :
    Measurable (finiteIncidenceNormGlobalCoverLabel ambient incidence
      ambientFamily fallback familyOfActive distance delta ceiling exponent
      globalScale hsymm) := by
  change Measurable (fun x =>
    finiteIncidenceNormGlobalCoverLabelValue ambientFamily fallback
      familyOfActive distance delta ceiling exponent globalScale hsymm
      (finiteIncidenceActiveAtPoint ambient incidence x))
  exact measurable_finiteIncidencePatternValue ambient incidence hincidence
    (finiteIncidenceNormGlobalCoverLabelValue ambientFamily fallback
      familyOfActive distance delta ceiling exponent globalScale hsymm)

set_option linter.unusedSectionVars false in
/-- Every label is one of the actual maximal-cover centres. -/
theorem finiteIncidenceNormGlobalCoverLabel_mem_centers
    (ambient : Finset index) (incidence : index → X → Prop)
    (ambientFamily : Finset alpha) (fallback : FiniteMetricMember ambientFamily)
    (familyOfActive : Finset index → Finset alpha)
    (distance : alpha → alpha → Real)
    (delta ceiling exponent globalScale : Real)
    (hsymm : ∀ f g, distance f g = distance g f) (x : X) :
    finiteIncidenceNormGlobalCoverLabel ambient incidence ambientFamily
        fallback familyOfActive distance delta ceiling exponent globalScale
        hsymm x ∈
      finiteMetricCoverCenters ambientFamily distance globalScale hsymm := by
  classical
  simp only [finiteIncidenceNormGlobalCoverLabel,
    finiteIncidenceNormGlobalCoverLabelValue]
  split_ifs with hfamily hcenter
  · exact finiteMetricCoverCode_mem_centers ambientFamily distance
      globalScale hsymm ⟨_, hcenter⟩
  · exact finiteMetricCoverCode_mem_centers ambientFamily distance
      globalScale hsymm fallback
  · exact finiteMetricCoverCode_mem_centers ambientFamily distance
      globalScale hsymm fallback

set_option linter.unusedSectionVars false in
/-- On a structurally valid nonempty pattern the label is exactly the code of
the canonical norm centre. -/
theorem finiteIncidenceNormGlobalCoverLabel_eq_code
    (ambient : Finset index) (incidence : index → X → Prop)
    (ambientFamily : Finset alpha) (fallback : FiniteMetricMember ambientFamily)
    (familyOfActive : Finset index → Finset alpha)
    (distance : alpha → alpha → Real)
    (delta ceiling exponent globalScale : Real)
    (hsymm : ∀ f g, distance f g = distance g f) (x : X)
    (hfamily : (familyOfActive
      (finiteIncidenceActiveAtPoint ambient incidence x)).Nonempty)
    (hsubset : familyOfActive
      (finiteIncidenceActiveAtPoint ambient incidence x) ⊆ ambientFamily) :
    finiteIncidenceNormGlobalCoverLabel ambient incidence ambientFamily
        fallback familyOfActive distance delta ceiling exponent globalScale
        hsymm x =
      finiteMetricCoverCode ambientFamily distance globalScale hsymm
        ⟨finiteCriticalMaximizerCenter
            (familyOfActive
              (finiteIncidenceActiveAtPoint ambient incidence x))
            distance delta ceiling exponent hfamily,
          hsubset (finiteCriticalMaximizerCenter_mem _ _ _ _ _ hfamily)⟩ := by
  simp only [finiteIncidenceNormGlobalCoverLabel,
    finiteIncidenceNormGlobalCoverLabelValue, dif_pos hfamily]
  rw [dif_pos]

set_option linter.style.haveILetI false in
/-- A genuine measurable `E_B` cell with the exact average-measure loss and
automatic pointwise `B_x ⊆ F_x ∩ 3B` cardinal retention. -/
theorem exists_normGlobalCoverCell_with_local_retention
    (mu : Measure X) (E : Set X) (hE : MeasurableSet E)
    (hEnonempty : E.Nonempty)
    (ambient : Finset index) (incidence : index → X → Prop)
    (hincidence : ∀ i ∈ ambient, MeasurableSet {x | incidence i x})
    (ambientFamily : Finset alpha)
    (familyOfActive : Finset index → Finset alpha)
    (distance : alpha → alpha → Real)
    {delta ceiling exponent globalScale : Real}
    (hfamily : ∀ x ∈ E,
      (familyOfActive
        (finiteIncidenceActiveAtPoint ambient incidence x)).Nonempty)
    (hsubset : ∀ active, familyOfActive active ⊆ ambientFamily)
    (hsymm : ∀ f g, distance f g = distance g f)
    (htriangle : ∀ f center g,
      distance f g ≤ distance f center + distance center g)
    (hself : ∀ f, f ∈ ambientFamily → distance f f = 0)
    (hdelta : 0 ≤ delta) (hdeltaCeiling : delta ≤ ceiling)
    (hglobalScale : 0 < globalScale)
    (hscaleUpper : ∀ x, ∀ hx : x ∈ E,
      finiteCriticalMaximizerScale
          (familyOfActive
            (finiteIncidenceActiveAtPoint ambient incidence x))
          distance delta ceiling exponent (hfamily x hx) ≤
        globalScale) :
    let centers := finiteMetricCoverCenters ambientFamily distance
      globalScale hsymm
    ∃ globalCenter ∈ centers, ∃ E_B : Set X,
      mu E / (centers.card : ENNReal) ≤ mu E_B ∧
      MeasurableSet E_B ∧ E_B ⊆ E ∧
      ∀ x, x ∈ E_B →
        let active := finiteIncidenceActiveAtPoint ambient incidence x
        let localFamily := familyOfActive active
        ∃ hlocalFamily : localFamily.Nonempty,
          let localBall := finiteNormCriticalBall localFamily distance delta
            ceiling exponent hlocalFamily
          let localized := finiteGlobalNormLocalizedFamily localFamily distance
            globalScale globalCenter
          localBall ⊆ localized ∧ localBall.card ≤ localized.card := by
  classical
  dsimp only
  obtain ⟨x0, hx0⟩ := hEnonempty
  obtain ⟨f0, hf0⟩ := hfamily x0 hx0
  have hf0Ambient := hsubset
    (finiteIncidenceActiveAtPoint ambient incidence x0) hf0
  let fallback : FiniteMetricMember ambientFamily := ⟨f0, hf0Ambient⟩
  let centers := finiteMetricCoverCenters ambientFamily distance globalScale
    hsymm
  have hcenters : centers.Nonempty :=
    finiteMetricCoverCenters_nonempty ambientFamily distance globalScale
      hsymm ⟨f0, hf0Ambient⟩
  let label := finiteIncidenceNormGlobalCoverLabel ambient incidence
    ambientFamily fallback familyOfActive distance delta ceiling exponent
    globalScale hsymm
  letI : MeasurableSpace alpha := ⊤
  letI : MeasurableSingletonClass alpha := ⟨fun _ => trivial⟩
  have hlabel : Measurable label :=
    measurable_finiteIncidenceNormGlobalCoverLabel ambient incidence hincidence
      ambientFamily fallback familyOfActive distance delta ceiling exponent
      globalScale hsymm
  have hlabelRange : ∀ x ∈ E, label x ∈ centers := by
    intro x _hx
    exact finiteIncidenceNormGlobalCoverLabel_mem_centers ambient incidence
      ambientFamily fallback familyOfActive distance delta ceiling exponent
      globalScale hsymm x
  obtain ⟨globalCenter, hglobalCenter, hmeasure⟩ :=
    exists_measurableLabelCell_measure_ge_average mu centers hcenters hE
      hlabel hlabelRange
  let E_B := measurableLabelCell E label globalCenter
  refine ⟨globalCenter, hglobalCenter, E_B, hmeasure,
    measurableSet_measurableLabelCell hE hlabel globalCenter, ?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro x hx
    have hxE : x ∈ E := hx.1
    let active := finiteIncidenceActiveAtPoint ambient incidence x
    let localFamily := familyOfActive active
    have hlocalFamily : localFamily.Nonempty := hfamily x hxE
    have hlocalSubset : localFamily ⊆ ambientFamily := hsubset active
    have hlabelEq : label x = globalCenter := by
      have hxLabel : label x ∈ ({globalCenter} : Set alpha) := hx.2
      simpa using hxLabel
    have hcodeEq :
        finiteMetricCoverCode ambientFamily distance globalScale hsymm
            ⟨finiteCriticalMaximizerCenter localFamily distance delta ceiling
                exponent hlocalFamily,
              hlocalSubset (finiteCriticalMaximizerCenter_mem _ _ _ _ _
                hlocalFamily)⟩ = globalCenter := by
      exact (finiteIncidenceNormGlobalCoverLabel_eq_code ambient incidence
        ambientFamily fallback familyOfActive distance delta ceiling exponent
        globalScale hsymm x hlocalFamily hlocalSubset).symm.trans hlabelEq
    have hlocal :=
      finiteNormCriticalBall_subset_global_code_localizedFamily
        localFamily ambientFamily distance hlocalFamily hlocalSubset hsymm
        htriangle hself hdelta hdeltaCeiling hglobalScale
        (hscaleUpper x hxE)
    have hlocal' :
        finiteNormCriticalBall localFamily distance delta ceiling exponent
            hlocalFamily ⊆
          finiteGlobalNormLocalizedFamily localFamily distance globalScale
            globalCenter := by
      simpa only [hcodeEq] using hlocal
    exact ⟨hlocalFamily, hlocal', Finset.card_le_card hlocal'⟩

#print axioms finiteIncidenceNormGlobalCoverLabelValue
#print axioms finiteIncidenceNormGlobalCoverLabel
#print axioms measurable_finiteIncidenceNormGlobalCoverLabel
#print axioms finiteIncidenceNormGlobalCoverLabel_mem_centers
#print axioms finiteIncidenceNormGlobalCoverLabel_eq_code
#print axioms exists_normGlobalCoverCell_with_local_retention

end

end FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1
