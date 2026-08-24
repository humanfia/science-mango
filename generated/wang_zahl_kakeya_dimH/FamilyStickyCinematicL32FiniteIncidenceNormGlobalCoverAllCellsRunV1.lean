import FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1

set_option autoImplicit false
set_option linter.style.haveILetI false

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverAllCellsRunV1

open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32FiniteIncidenceCanonicalCriticalCenterV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1

noncomputable section

/-!
# All measurable cells of the global norm cover

The paper sums over the finitely-overlapping norm balls.  This module keeps
every measurable label cell, proves their exact measure decomposition, and
derives the local critical-ball containment on each cell.  It is the
all-centre replacement for the earlier one-cell pigeonhole theorem.
-/

universe u v w

variable {X : Type u} {index : Type v} {alpha : Type w}
  [MeasurableSpace X] [DecidableEq alpha]

/-- Exact all-centre decomposition together with the automatically produced
critical-ball localization on every cell. -/
theorem exists_normGlobalCoverAllCells_with_local_retention
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
    ∃ fallback : FiniteMetricMember ambientFamily,
      let centers := finiteMetricCoverCenters ambientFamily distance
        globalScale hsymm
      let label := finiteIncidenceNormGlobalCoverLabel ambient incidence
        ambientFamily fallback familyOfActive distance delta ceiling exponent
        globalScale hsymm
      mu E = ∑ center ∈ centers,
          mu (measurableLabelCell E label center) ∧
      (∀ x ∈ E, label x ∈ centers) ∧
      ∀ center, center ∈ centers →
        MeasurableSet (measurableLabelCell E label center) ∧
        measurableLabelCell E label center ⊆ E ∧
        ∀ x, x ∈ measurableLabelCell E label center →
          let active := finiteIncidenceActiveAtPoint ambient incidence x
          let localFamily := familyOfActive active
          ∃ hlocalFamily : localFamily.Nonempty,
            let localBall := finiteNormCriticalBall localFamily distance delta
              ceiling exponent hlocalFamily
            let localized := finiteGlobalNormLocalizedFamily localFamily
              distance globalScale center
            localBall ⊆ localized ∧ localBall.card ≤ localized.card := by
  classical
  obtain ⟨x0, hx0⟩ := hEnonempty
  obtain ⟨f0, hf0⟩ := hfamily x0 hx0
  have hf0Ambient := hsubset
    (finiteIncidenceActiveAtPoint ambient incidence x0) hf0
  let fallback : FiniteMetricMember ambientFamily := ⟨f0, hf0Ambient⟩
  refine ⟨fallback, ?_⟩
  dsimp only
  let centers := finiteMetricCoverCenters ambientFamily distance globalScale
    hsymm
  let label := finiteIncidenceNormGlobalCoverLabel ambient incidence
    ambientFamily fallback familyOfActive distance delta ceiling exponent
    globalScale hsymm
  letI : MeasurableSpace alpha := ⊤
  letI : MeasurableSingletonClass alpha := ⟨fun _ ↦ trivial⟩
  have hlabel : Measurable label :=
    measurable_finiteIncidenceNormGlobalCoverLabel ambient incidence hincidence
      ambientFamily fallback familyOfActive distance delta ceiling exponent
      globalScale hsymm
  have hlabelRange : ∀ x ∈ E, label x ∈ centers := by
    intro x _hx
    exact finiteIncidenceNormGlobalCoverLabel_mem_centers ambient incidence
      ambientFamily fallback familyOfActive distance delta ceiling exponent
      globalScale hsymm x
  have hpartition :
      mu E = ∑ center ∈ centers,
          mu (measurableLabelCell E label center) :=
    measure_eq_sum_measurableLabelCell mu centers hE hlabel hlabelRange
  refine ⟨hpartition, hlabelRange, ?_⟩
  intro center hcenter
  refine ⟨measurableSet_measurableLabelCell hE hlabel center, ?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro x hx
    have hxE : x ∈ E := hx.1
    let active := finiteIncidenceActiveAtPoint ambient incidence x
    let localFamily := familyOfActive active
    have hlocalFamily : localFamily.Nonempty := hfamily x hxE
    have hlocalSubset : localFamily ⊆ ambientFamily := hsubset active
    have hlabelEq : label x = center := by
      have hxLabel : label x ∈ ({center} : Set alpha) := hx.2
      simpa using hxLabel
    have hcodeEq :
        finiteMetricCoverCode ambientFamily distance globalScale hsymm
            ⟨finiteCriticalMaximizerCenter localFamily distance delta ceiling
                exponent hlocalFamily,
              hlocalSubset (finiteCriticalMaximizerCenter_mem _ _ _ _ _
                hlocalFamily)⟩ = center := by
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
            center := by
      simpa only [hcodeEq] using hlocal
    exact ⟨hlocalFamily, hlocal', Finset.card_le_card hlocal'⟩

#print axioms exists_normGlobalCoverAllCells_with_local_retention

end

end FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverAllCellsRunV1
