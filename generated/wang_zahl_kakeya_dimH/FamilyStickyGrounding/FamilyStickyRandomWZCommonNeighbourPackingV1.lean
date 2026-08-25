import FamilyStickyGrounding.FamilyStickyRandomWZLineParameterGeometryV1

open Set
open scoped NNReal

namespace FamilyStickyRandomWZCommonNeighbourPackingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomProductCoordinatePackingV1
open FamilyStickyRandomHundredContainerSelectionV1
open FamilyStickyRandomHundredContainerSelectionV1.MaximalSelection
open FamilyStickyRandomWZLineParameterGeometryV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Uniform packing of common-`100` neighbours

Fix an active source tube `b`.  Every member `a` of its literal
`commonHundredNeighbourFinset` shares some `100 W_a` container with `b`.
The actual parameter geometry chooses orientations of both `a` and `b` in
that container and puts their oriented parameters within `1200 delta`.

The chosen orientation of `b` has only two values.  After translating by
that presentation of `b` and rescaling by `delta^{-1}`, each neighbour lies
in the fixed radius-`1200` product-coordinate ball.  Source pairwise WZ
endpoint-parameter separation gives normalized separation at least one
inside each of the two orientation classes.  Coding by

`Bool x canonicalPackingNet.centers`

is therefore injective.  This proves the dimension-only bound
`2 * productCoordinatePackingConstant` and eliminates the previously exact
but uncontrolled common-neighbour multiplicity.

The source hypothesis here is the formal projective endpoint-parameter cell
predicate from the preceding module.  It is the thin interface to be
produced by the exact WZ1 line-space refinement; Family4 volume-overlap
essential distinctness remains insufficient and is not used.
-/

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- The actual finite common-neighbour occurrence type. -/
abbrev CommonNeighbour
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (b : ActiveSource G) :=
  {a // a ∈ commonHundredNeighbourFinset G b}

theorem commonHundredContainer_of_mem_neighbour
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (b : ActiveSource G) (a : CommonNeighbour G b) :
    CommonHundredContainer (G.tube a.1.1) (G.tube b.1) := by
  classical
  have hor := (Finset.mem_filter.mp a.2).2
  rcases hor with heq | hcommon
  · simpa only [heq] using commonHundredContainer_self (G.tube b.1)
  · exact hcommon

/-- Automatically chosen common-container parameter data for one neighbour. -/
def neighbourParameterData
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (b : ActiveSource G) (a : CommonNeighbour G b) :
    CommonContainerParameterData (G.tube a.1.1) (G.tube b.1) :=
  Classical.choice
    (FamilyStickyRandomWZLineParameterGeometryV1.CommonHundredContainer.parameterData
      (commonHundredContainer_of_mem_neighbour G b a))

/-- Which of the two projective presentations of the centre tube was chosen
for this neighbour. -/
def neighbourCenterOrientation
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (b : ActiveSource G) (a : CommonNeighbour G b) : Bool :=
  (neighbourParameterData G b a).U_orientation

/-- Translate by the chosen presentation of the centre tube and normalize
the line cell to unit separation scale. -/
def normalizedNeighbourParameter
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (b : ActiveSource G) (a : CommonNeighbour G b) : LineParameter :=
  ((delta : Real)⁻¹) •
    (orientedLineParameter (G.tube a.1.1)
        (neighbourParameterData G b a).T_orientation -
      orientedLineParameter (G.tube b.1)
        (neighbourParameterData G b a).U_orientation)

theorem norm_inv_smul_le_twelveHundred
    {delta : NNReal} (hdelta : 0 < delta) {x : LineParameter}
    (hx : ‖x‖ <= 1200 * (delta : Real)) :
    ‖((delta : Real)⁻¹) • x‖ <= 1200 := by
  have hdeltaReal : (0 : Real) < (delta : Real) := by exact_mod_cast hdelta
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdeltaReal)]
  calc
    (delta : Real)⁻¹ * ‖x‖ <=
        (delta : Real)⁻¹ * (1200 * (delta : Real)) :=
      mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hdeltaReal.le)
    _ = 1200 := by field_simp

theorem normalizedNeighbourParameter_norm_le
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hdelta : 0 < delta) (b : ActiveSource G)
    (a : CommonNeighbour G b) :
    ‖normalizedNeighbourParameter G b a‖ <=
      (normalizedParameterRadius : Real) := by
  apply norm_inv_smul_le_twelveHundred hdelta
  exact (neighbourParameterData G b a).parameters_near

theorem normalizedNeighbourParameter_one_separated_of_sameCenterOrientation
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (G.tubes : Set tubeIndex) fun i j =>
      WZEndpointParameterSeparated (G.tube i) (G.tube j))
    (b : ActiveSource G) {a c : CommonNeighbour G b}
    (hac : a ≠ c)
    (horientation : neighbourCenterOrientation G b a =
      neighbourCenterOrientation G b c) :
    1 <= ‖normalizedNeighbourParameter G b a -
      normalizedNeighbourParameter G b c‖ := by
  let Da := neighbourParameterData G b a
  let Dc := neighbourParameterData G b c
  have hacIndex : a.1.1 ≠ c.1.1 := by
    intro hindex
    apply hac
    apply Subtype.ext
    exact Subtype.ext hindex
  have hsource := hpair a.1.2 c.1.2 hacIndex
  have hraw : (delta : Real) <=
      ‖orientedLineParameter (G.tube a.1.1) Da.T_orientation -
        orientedLineParameter (G.tube c.1.1) Dc.T_orientation‖ :=
    hsource Da.T_orientation Dc.T_orientation
  have hcenter :
      orientedLineParameter (G.tube b.1) Da.U_orientation =
        orientedLineParameter (G.tube b.1) Dc.U_orientation := by
    have horientation' : Da.U_orientation = Dc.U_orientation := by
      simpa [neighbourCenterOrientation, Da, Dc] using horientation
    rw [horientation']
  have hvector :
      normalizedNeighbourParameter G b a -
          normalizedNeighbourParameter G b c =
        ((delta : Real)⁻¹) •
          (orientedLineParameter (G.tube a.1.1) Da.T_orientation -
            orientedLineParameter (G.tube c.1.1) Dc.T_orientation) := by
    unfold normalizedNeighbourParameter
    change ((delta : Real)⁻¹) •
          (orientedLineParameter (G.tube a.1.1) Da.T_orientation -
            orientedLineParameter (G.tube b.1) Da.U_orientation) -
        ((delta : Real)⁻¹) •
          (orientedLineParameter (G.tube c.1.1) Dc.T_orientation -
            orientedLineParameter (G.tube b.1) Dc.U_orientation) = _
    rw [hcenter]
    module
  rw [hvector, norm_smul, Real.norm_eq_abs]
  have hdeltaReal : (0 : Real) < (delta : Real) := by exact_mod_cast hdelta
  rw [abs_of_pos (inv_pos.mpr hdeltaReal)]
  calc
    (1 : Real) = (delta : Real)⁻¹ * (delta : Real) := by field_simp
    _ <= (delta : Real)⁻¹ *
        ‖orientedLineParameter (G.tube a.1.1) Da.T_orientation -
          orientedLineParameter (G.tube c.1.1) Dc.T_orientation‖ :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hdeltaReal.le)

/-- Code one neighbour by the centre orientation class and the canonical
finite product-coordinate net. -/
def neighbourPackingCode
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hdelta : 0 < delta) (b : ActiveSource G)
    (a : CommonNeighbour G b) :
    Bool × {p // p ∈ canonicalPackingNet.centers} :=
  (neighbourCenterOrientation G b a,
    canonicalPackingNet.code (normalizedNeighbourParameter G b)
      (normalizedNeighbourParameter_norm_le G hdelta b) a)

theorem neighbourPackingCode_injective
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (G.tubes : Set tubeIndex) fun i j =>
      WZEndpointParameterSeparated (G.tube i) (G.tube j))
    (b : ActiveSource G) :
    Function.Injective (neighbourPackingCode G hdelta b) := by
  intro a c hcode
  by_contra hac
  have horientation : neighbourCenterOrientation G b a =
      neighbourCenterOrientation G b c :=
    congrArg Prod.fst hcode
  have hnetCode :
      canonicalPackingNet.code (normalizedNeighbourParameter G b)
          (normalizedNeighbourParameter_norm_le G hdelta b) a =
        canonicalPackingNet.code (normalizedNeighbourParameter G b)
          (normalizedNeighbourParameter_norm_le G hdelta b) c :=
    congrArg Prod.snd hcode
  have hsep : (1 : Real) <=
      dist (normalizedNeighbourParameter G b a)
        (normalizedNeighbourParameter G b c) := by
    simpa [dist_eq_norm] using
      normalizedNeighbourParameter_one_separated_of_sameCenterOrientation
        G hdelta hpair b hac horientation
  have hnearA := canonicalPackingNet.dist_parameter_code_le
    (normalizedNeighbourParameter G b)
    (normalizedNeighbourParameter_norm_le G hdelta b) a
  have hnearC := canonicalPackingNet.dist_parameter_code_le
    (normalizedNeighbourParameter G b)
    (normalizedNeighbourParameter_norm_le G hdelta b) c
  have hlt : dist (normalizedNeighbourParameter G b a)
      (normalizedNeighbourParameter G b c) < 1 := by
    calc
      dist (normalizedNeighbourParameter G b a)
          (normalizedNeighbourParameter G b c) <=
        dist (normalizedNeighbourParameter G b a)
            (canonicalPackingNet.code (normalizedNeighbourParameter G b)
              (normalizedNeighbourParameter_norm_le G hdelta b) a).1 +
          dist (canonicalPackingNet.code (normalizedNeighbourParameter G b)
              (normalizedNeighbourParameter_norm_le G hdelta b) a).1
            (normalizedNeighbourParameter G b c) := dist_triangle _ _ _
      _ = dist (normalizedNeighbourParameter G b a)
            (canonicalPackingNet.code (normalizedNeighbourParameter G b)
              (normalizedNeighbourParameter_norm_le G hdelta b) a).1 +
          dist (canonicalPackingNet.code (normalizedNeighbourParameter G b)
              (normalizedNeighbourParameter_norm_le G hdelta b) c).1
            (normalizedNeighbourParameter G b c) := by rw [hnetCode]
      _ <= (4 : Real)⁻¹ + (4 : Real)⁻¹ := by
        exact add_le_add hnearA (by simpa [dist_comm] using hnearC)
      _ < 1 := by norm_num
  exact (not_lt_of_ge hsep) hlt

/-- The paper's dimension-only common-neighbour constant.  The factor two is
exactly the two projective orientations of the centre segment. -/
def commonHundredNeighbourPackingConstant : Nat :=
  2 * productCoordinatePackingConstant

theorem commonHundredNeighbourFinset_card_le_constant
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (G.tubes : Set tubeIndex) fun i j =>
      WZEndpointParameterSeparated (G.tube i) (G.tube j))
    (b : ActiveSource G) :
    (commonHundredNeighbourFinset G b).card <=
      commonHundredNeighbourPackingConstant := by
  have hcard := Fintype.card_le_of_injective
    (neighbourPackingCode G hdelta b)
    (neighbourPackingCode_injective G hdelta hpair b)
  simpa [commonHundredNeighbourPackingConstant,
    productCoordinatePackingConstant] using hcard

theorem commonHundredNeighbourMultiplicity_le_constant
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (G.tubes : Set tubeIndex) fun i j =>
      WZEndpointParameterSeparated (G.tube i) (G.tube j)) :
    commonHundredNeighbourMultiplicity G <=
      commonHundredNeighbourPackingConstant := by
  unfold commonHundredNeighbourMultiplicity
  apply Finset.sup_le
  intro b _hb
  exact commonHundredNeighbourFinset_card_le_constant G hdelta hpair b

/-- Quantitative maximal-selection loss with a genuine dimension-only
constant, rather than the uncontrolled exact neighbourhood supremum. -/
theorem active_card_le_constant_mul_selected_card
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (G.tubes : Set tubeIndex) fun i j =>
      WZEndpointParameterSeparated (G.tube i) (G.tube j)) :
    Fintype.card (ActiveSource G) <=
      commonHundredNeighbourPackingConstant *
        Fintype.card (SelectedSource G) := by
  exact (active_card_le_multiplicity_mul_selected_card G).trans
    (Nat.mul_le_mul_right (Fintype.card (SelectedSource G))
      (commonHundredNeighbourMultiplicity_le_constant G hdelta hpair))

#print axioms commonHundredContainer_of_mem_neighbour
#print axioms normalizedNeighbourParameter_norm_le
#print axioms normalizedNeighbourParameter_one_separated_of_sameCenterOrientation
#print axioms neighbourPackingCode_injective
#print axioms commonHundredNeighbourFinset_card_le_constant
#print axioms commonHundredNeighbourMultiplicity_le_constant
#print axioms active_card_le_constant_mul_selected_card

end
end FamilyStickyRandomWZCommonNeighbourPackingV1
