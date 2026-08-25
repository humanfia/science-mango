import FamilyStickyGrounding.FamilyStickyWZ2CinematicTranslationV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace FamilyStickyWZ2ReducedParameterClusterWindowV1

open FamilyStickyWZ2CinematicTranslationV1

noncomputable section

/-!
# Cluster-to-window reduction for WZ2 reduced parameters

The fixed-`c` WZ2 copy action is componentwise addition on `(a,b,d)`.  If a
source parameter family lies in a radius-`rho` coordinate window, every copy
that meets a radius-`R` test window has its shift in the enlarged radius
`R + rho` window.  The resulting finite-cardinality theorem is the exact
interface used by an explicit shift-grid packing argument.
-/

/-- Coordinate-sup distance on the reduced `(a,b,d)` parameter space. -/
def reducedParameterDistance (p q : ReducedLineParameter) : Real :=
  max |p.1 - q.1| (max |p.2.1 - q.2.1| |p.2.2 - q.2.2|)

theorem reducedParameterDistance_nonneg (p q : ReducedLineParameter) :
    0 <= reducedParameterDistance p q := by
  exact le_trans (abs_nonneg _) (le_max_left _ _)

theorem abs_fst_sub_le_reducedParameterDistance
    (p q : ReducedLineParameter) :
    |p.1 - q.1| <= reducedParameterDistance p q := by
  exact le_max_left _ _

theorem abs_snd_fst_sub_le_reducedParameterDistance
    (p q : ReducedLineParameter) :
    |p.2.1 - q.2.1| <= reducedParameterDistance p q := by
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem abs_snd_snd_sub_le_reducedParameterDistance
    (p q : ReducedLineParameter) :
    |p.2.2 - q.2.2| <= reducedParameterDistance p q := by
  exact (le_max_right _ _).trans (le_max_right _ _)

/-- Componentwise difference in reduced parameter space. -/
def reducedParameterSub (p q : ReducedLineParameter) : ReducedLineParameter :=
  (p.1 - q.1, (p.2.1 - q.2.1, p.2.2 - q.2.2))

/-- Indices whose reduced parameters lie in one closed coordinate-sup
window. -/
def parameterWindowIndices
    {index : Type*} [Fintype index] [DecidableEq index]
    (parameter : index -> ReducedLineParameter)
    (center : ReducedLineParameter) (radius : Real) : Finset index :=
  Finset.univ.filter fun i =>
    reducedParameterDistance (parameter i) center <= radius

/-- Product indices whose translated parameters lie in one closed window. -/
def translatedParameterWindowIndices
    {tau kappa : Type*}
    [Fintype tau] [DecidableEq tau]
    [Fintype kappa] [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (parameter : kappa -> ReducedLineParameter)
    (center : ReducedLineParameter) (radius : Real) : Finset (tau × kappa) :=
  Finset.univ.filter fun ji =>
    reducedParameterDistance
      (translateReducedLineParameter
        (shift ji.1).1 (shift ji.1).2.1 (shift ji.1).2.2
        (parameter ji.2)) center <= radius

/-- A translated hit forces the copy shift into the enlarged window around
`center - base`. -/
theorem shift_mem_enlarged_window_of_translated_mem
    {tau kappa : Type*}
    (shift : tau -> ReducedLineParameter)
    (parameter : kappa -> ReducedLineParameter)
    (base center : ReducedLineParameter) {rho radius : Real}
    (hcluster : forall i,
      reducedParameterDistance (parameter i) base <= rho)
    {j : tau} {i : kappa}
    (htranslated :
      reducedParameterDistance
        (translateReducedLineParameter
          (shift j).1 (shift j).2.1 (shift j).2.2 (parameter i)) center <=
        radius) :
    reducedParameterDistance (shift j) (reducedParameterSub center base) <=
      radius + rho := by
  apply max_le
  · calc
      |(shift j).1 - (reducedParameterSub center base).1| =
          |((parameter i).1 + (shift j).1 - center.1) -
            ((parameter i).1 - base.1)| := by
          simp only [reducedParameterSub]
          congr 1
          ring
      _ <= |(parameter i).1 + (shift j).1 - center.1| +
          |(parameter i).1 - base.1| := abs_sub _ _
      _ <= radius + rho := add_le_add
        ((abs_fst_sub_le_reducedParameterDistance _ _).trans htranslated)
        ((abs_fst_sub_le_reducedParameterDistance _ _).trans (hcluster i))
  · apply max_le
    · calc
        |(shift j).2.1 - (reducedParameterSub center base).2.1| =
            |((parameter i).2.1 + (shift j).2.1 - center.2.1) -
              ((parameter i).2.1 - base.2.1)| := by
            simp only [reducedParameterSub]
            congr 1
            ring
        _ <= |(parameter i).2.1 + (shift j).2.1 - center.2.1| +
            |(parameter i).2.1 - base.2.1| := abs_sub _ _
        _ <= radius + rho := add_le_add
          ((abs_snd_fst_sub_le_reducedParameterDistance _ _).trans
            htranslated)
          ((abs_snd_fst_sub_le_reducedParameterDistance _ _).trans
            (hcluster i))
    · calc
        |(shift j).2.2 - (reducedParameterSub center base).2.2| =
            |((parameter i).2.2 + (shift j).2.2 - center.2.2) -
              ((parameter i).2.2 - base.2.2)| := by
            simp only [reducedParameterSub]
            congr 1
            ring
        _ <= |(parameter i).2.2 + (shift j).2.2 - center.2.2| +
            |(parameter i).2.2 - base.2.2| := abs_sub _ _
        _ <= radius + rho := add_le_add
          ((abs_snd_snd_sub_le_reducedParameterDistance _ _).trans
            htranslated)
          ((abs_snd_snd_sub_le_reducedParameterDistance _ _).trans
            (hcluster i))

/-- Finite cluster-to-shift occupancy reduction.  The product-window count
is controlled by the source cardinality times the number of locally relevant
copy shifts. -/
theorem card_translatedParameterWindowIndices_le_card_mul_shiftWindow
    {tau kappa : Type*}
    [Fintype tau] [DecidableEq tau]
    [Fintype kappa] [DecidableEq kappa]
    (shift : tau -> ReducedLineParameter)
    (parameter : kappa -> ReducedLineParameter)
    (base center : ReducedLineParameter) {rho radius : Real}
    (hcluster : forall i,
      reducedParameterDistance (parameter i) base <= rho) :
    (translatedParameterWindowIndices shift parameter center radius).card <=
      Fintype.card kappa *
        (parameterWindowIndices shift (reducedParameterSub center base)
          (radius + rho)).card := by
  classical
  have hsubset :
      translatedParameterWindowIndices shift parameter center radius <=
        (parameterWindowIndices shift (reducedParameterSub center base)
          (radius + rho)) ×ˢ (Finset.univ : Finset kappa) := by
    intro ji hji
    rw [Finset.mem_product]
    constructor
    · rw [parameterWindowIndices, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      exact shift_mem_enlarged_window_of_translated_mem
        shift parameter base center hcluster
        (Finset.mem_filter.mp hji).2
    · exact Finset.mem_univ _
  calc
    (translatedParameterWindowIndices shift parameter center radius).card <=
        ((parameterWindowIndices shift (reducedParameterSub center base)
          (radius + rho)) ×ˢ (Finset.univ : Finset kappa)).card :=
      Finset.card_le_card hsubset
    _ = Fintype.card kappa *
        (parameterWindowIndices shift (reducedParameterSub center base)
          (radius + rho)).card := by
      simp [Nat.mul_comm]

#print axioms reducedParameterDistance_nonneg
#print axioms shift_mem_enlarged_window_of_translated_mem
#print axioms card_translatedParameterWindowIndices_le_card_mul_shiftWindow

end
end FamilyStickyWZ2ReducedParameterClusterWindowV1
