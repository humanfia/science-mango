import FamilyStickyGrounding.FamilyStickyWZ2ShearParameterPackingV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal BigOperators

namespace FamilyStickyWZ2ShearParameterNonconcentrationV1

open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyWZ2ReducedParameterClusterWindowV1
open FamilyStickyWZ2ShearParameterPackingV1

noncomputable section

/-!
# Local nonconcentration of the translated WZ2 parameter family

The preceding grid theorem bounds the locally relevant copy sites.  This
module also retains the source family's local window bound inside each copy.
Fiberwise counting therefore gives the product of the source-window budget
and the local shear-site budget, capped by the total copy count.  This is the
finite parameter-space analogue of WZ2's translated-copy construction.
-/

/-- Componentwise reduced-parameter translation is an isometry for the
coordinate-sup distance. -/
theorem reducedParameterDistance_translate_eq
    (shift p q : ReducedLineParameter) :
    reducedParameterDistance
      (translateReducedLineParameter shift.1 shift.2.1 shift.2.2 p) q =
      reducedParameterDistance p (reducedParameterSub q shift) := by
  simp only [reducedParameterDistance, translateReducedLineParameter,
    reducedParameterSub]
  congr 1
  · congr 1
    ring
  · congr 1
    · congr 1
      ring
    · congr 1
      ring

/-- Fiberwise cluster-to-shift count.  In addition to bounding the number of
relevant shifts, it uses the source's own local window budget at the same
test radius. -/
theorem card_translatedParameterWindowIndices_le_shiftWindow_mul_sourceBudget
    {tau kappa : Type*}
    [Fintype tau] [DecidableEq tau]
    [Fintype kappa] [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (parameter : kappa -> ReducedLineParameter)
    (base center : ReducedLineParameter) {rho radius : Real}
    (hcluster : forall i,
      reducedParameterDistance (parameter i) base <= rho)
    (sourceBudget : Nat)
    (hsource : forall q,
      (parameterWindowIndices parameter q radius).card <= sourceBudget) :
    (translatedParameterWindowIndices shift parameter center radius).card <=
      (parameterWindowIndices shift (reducedParameterSub center base)
        (radius + rho)).card * sourceBudget := by
  classical
  let active : Finset (tau × kappa) :=
    translatedParameterWindowIndices shift parameter center radius
  let relevant : Finset tau :=
    parameterWindowIndices shift (reducedParameterSub center base)
      (radius + rho)
  have hmaps : (active : Set (tau × kappa)).MapsTo Prod.fst relevant := by
    intro ji hji
    change ji.1 ∈ parameterWindowIndices shift
      (reducedParameterSub center base) (radius + rho)
    rw [parameterWindowIndices, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact shift_mem_enlarged_window_of_translated_mem
      shift parameter base center hcluster
      (Finset.mem_filter.mp hji).2
  rw [show (translatedParameterWindowIndices shift parameter center radius) =
      active from rfl]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    (∑ j ∈ relevant,
        ((active.filter fun ji => ji.1 = j).card)) <=
        ∑ _j ∈ relevant, sourceBudget := by
      apply Finset.sum_le_sum
      intro j _hj
      let fiber : Finset (tau × kappa) :=
        active.filter fun ji => ji.1 = j
      let sourceWindow : Finset kappa :=
        parameterWindowIndices parameter
          (reducedParameterSub center (shift j)) radius
      let encode : {ji // ji ∈ fiber} -> {i // i ∈ sourceWindow} :=
        fun ji => ⟨ji.1.2, by
          change ji.1.2 ∈ parameterWindowIndices parameter
            (reducedParameterSub center (shift j)) radius
          rw [parameterWindowIndices, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hactive := (Finset.mem_filter.mp ji.2).1
          have hfst := (Finset.mem_filter.mp ji.2).2
          have hdistance := (Finset.mem_filter.mp hactive).2
          rw [hfst] at hdistance
          rwa [← reducedParameterDistance_translate_eq (shift j)
            (parameter ji.1.2) center]⟩
      have hencode : Function.Injective encode := by
        intro x y hxy
        apply Subtype.ext
        apply Prod.ext
        · have hx := (Finset.mem_filter.mp x.2).2
          have hy := (Finset.mem_filter.mp y.2).2
          exact hx.trans hy.symm
        · exact congrArg Subtype.val hxy
      have hcard := Fintype.card_le_of_injective encode hencode
      have hfiber : fiber.card <= sourceWindow.card := by
        simpa only [Fintype.card_coe] using hcard
      exact hfiber.trans (hsource (reducedParameterSub center (shift j)))
    _ = relevant.card * sourceBudget := by simp

/-- Explicit WZ2 shear-copy nonconcentration.  The source window budget is
multiplied by the minimum of the total copy count and the locally derived
ceiling budget. -/
theorem card_shearGrid_translatedParameterWindow_le_local
    {siteCount : Nat} {kappa : Type*}
    [Fintype kappa] [DecidableEq kappa]
    (parameter : kappa -> ReducedLineParameter)
    (base center : ReducedLineParameter)
    {spacing rho radius : Real}
    (hspacing : 0 < spacing) (hrho : 0 <= rho) (hradius : 0 <= radius)
    (hcluster : forall i,
      reducedParameterDistance (parameter i) base <= rho)
    (sourceBudget : Nat)
    (hsource : forall q,
      (parameterWindowIndices parameter q radius).card <= sourceBudget) :
    (translatedParameterWindowIndices
      (shearReducedShift spacing (siteCount := siteCount))
      parameter center radius).card <=
      min siteCount (shearShiftHitBudget spacing (radius + rho)) *
        sourceBudget := by
  rw [min_mul]
  apply Nat.le_min.mpr
  constructor
  · calc
      (translatedParameterWindowIndices
        (shearReducedShift spacing (siteCount := siteCount))
        parameter center radius).card <=
          (parameterWindowIndices
            (shearReducedShift spacing (siteCount := siteCount))
            (reducedParameterSub center base) (radius + rho)).card *
              sourceBudget :=
        card_translatedParameterWindowIndices_le_shiftWindow_mul_sourceBudget
          (shearReducedShift spacing (siteCount := siteCount)) parameter
          base center hcluster sourceBudget hsource
      _ <= siteCount * sourceBudget := by
        gcongr
        have hcard :
            (parameterWindowIndices
              (shearReducedShift spacing (siteCount := siteCount))
              (reducedParameterSub center base) (radius + rho)).card <=
              (Finset.univ : Finset (Fin siteCount)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        simpa using hcard
  · calc
      (translatedParameterWindowIndices
        (shearReducedShift spacing (siteCount := siteCount))
        parameter center radius).card <=
          (parameterWindowIndices
            (shearReducedShift spacing (siteCount := siteCount))
            (reducedParameterSub center base) (radius + rho)).card *
              sourceBudget :=
        card_translatedParameterWindowIndices_le_shiftWindow_mul_sourceBudget
          (shearReducedShift spacing (siteCount := siteCount)) parameter
          base center hcluster sourceBudget hsource
      _ <= shearShiftHitBudget spacing (radius + rho) * sourceBudget := by
        gcongr
        exact card_shearReducedShift_window_le_hitBudget hspacing
          (add_nonneg hradius hrho) (reducedParameterSub center base)

#print axioms reducedParameterDistance_translate_eq
#print axioms card_translatedParameterWindowIndices_le_shiftWindow_mul_sourceBudget
#print axioms card_shearGrid_translatedParameterWindow_le_local

end
end FamilyStickyWZ2ShearParameterNonconcentrationV1
