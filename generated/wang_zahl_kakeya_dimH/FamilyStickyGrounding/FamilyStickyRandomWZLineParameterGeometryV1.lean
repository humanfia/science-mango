import FamilyStickyGrounding.FamilyStickyRandomProductCoordinatePackingV1
import FamilyStickyGrounding.FamilyStickyRandomHundredContainerSelectionV1
import FamilyStickyGrounding.FamilyStickyTubeParentDirectionCoherenceV1

open Set
open scoped NNReal

namespace FamilyStickyRandomWZLineParameterGeometryV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyRandomProductCoordinatePackingV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomHundredContainerSelectionV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Actual tubes in an oriented WZ line-parameter cell

WZ1 measures separation in line space by a basepoint term plus a direction
term; the direction is projective.  For a unit segment there are exactly two
oriented presentations: `(base,direction)` and `(endpoint,-direction)`.

If the carrier of a `delta`-tube `T` lies in a literal `100 W`, the existing
common-segment endpoint-pairing theorem chooses one of those presentations
whose basepoint is within `300 delta` of `W.base` and whose direction is
within `600 delta` of `W.direction`.  Consequently its product parameter in
`Space x Space` is within `600 delta` of the container parameter.

This is the actual Tube-to-parameter proximity producer.  The separation
predicate below is deliberately stated on both projective presentations; a
later source adapter must derive it from the exact WZ line-cell refinement.
It is not identified with the repository's unrelated Family4 volume-overlap
predicate.
-/

/-- One of the two oriented presentations of the same unit segment. -/
def orientedLineParameter {delta : NNReal} (T : Tube delta)
    (reverse : Bool) : LineParameter :=
  if reverse then (T.axis.endpoint, -T.axis.direction)
  else (T.axis.base, T.axis.direction)

@[simp] theorem orientedLineParameter_false {delta : NNReal}
    (T : Tube delta) :
    orientedLineParameter T false = (T.axis.base, T.axis.direction) := rfl

@[simp] theorem orientedLineParameter_true {delta : NNReal}
    (T : Tube delta) :
    orientedLineParameter T true = (T.axis.endpoint, -T.axis.direction) := rfl

/-- The reference presentation of the container axis. -/
def containerLineParameter {delta : NNReal} (W : Tube delta) :
    LineParameter := (W.axis.base, W.axis.direction)

/-- Projective endpoint-parameter separation.  It guarantees separation for
whatever orientations are selected by a common container. -/
def WZEndpointParameterSeparated {delta : NNReal} (T U : Tube delta) : Prop :=
  forall e f : Bool,
    (delta : Real) <=
      ‖orientedLineParameter T e - orientedLineParameter U f‖

theorem direction_gap_le_two_mul_of_forward_endpoint_pairing
    (S L : UnitSegment) {r : Real}
    (hbase : dist S.base L.base <= r)
    (hend : dist S.endpoint L.endpoint <= r) :
    ‖L.direction - S.direction‖ <= 2 * r := by
  calc
    ‖L.direction - S.direction‖ =
        ‖(L.endpoint - S.endpoint) + (S.base - L.base)‖ := by
      congr 1
      simp only [UnitSegment.endpoint]
      module
    _ <= ‖L.endpoint - S.endpoint‖ + ‖S.base - L.base‖ :=
      norm_add_le _ _
    _ = dist L.endpoint S.endpoint + dist S.base L.base := by
      rw [dist_eq_norm, dist_eq_norm]
    _ = dist S.endpoint L.endpoint + dist S.base L.base := by
      rw [dist_comm L.endpoint S.endpoint]
    _ <= 2 * r := by linarith

theorem reverse_direction_gap_le_two_mul_of_reverse_endpoint_pairing
    (S L : UnitSegment) {r : Real}
    (hbase : dist S.base L.endpoint <= r)
    (hend : dist S.endpoint L.base <= r) :
    ‖-L.direction - S.direction‖ <= 2 * r := by
  calc
    ‖-L.direction - S.direction‖ =
        ‖(L.base - S.endpoint) + (S.base - L.endpoint)‖ := by
      congr 1
      simp only [UnitSegment.endpoint]
      module
    _ <= ‖L.base - S.endpoint‖ + ‖S.base - L.endpoint‖ :=
      norm_add_le _ _
    _ = dist L.base S.endpoint + dist S.base L.endpoint := by
      rw [dist_eq_norm, dist_eq_norm]
    _ = dist S.endpoint L.base + dist S.base L.endpoint := by
      rw [dist_comm L.base S.endpoint]
    _ <= 2 * r := by linarith

/-- Componentwise actual proximity to a `100 W` container. -/
theorem exists_orientation_componentwise_near_hundredContainer
    {delta : NNReal} (T W : Tube delta)
    (hT : T.carrier ⊆ (hundredTube W).carrier) :
    exists e : Bool,
      ‖(orientedLineParameter T e).1 - W.axis.base‖ <=
          300 * (delta : Real) ∧
      ‖(orientedLineParameter T e).2 - W.axis.direction‖ <=
          600 * (delta : Real) := by
  have haxis : T.axis.carrier ⊆ (hundredTube W).carrier :=
    T.axis_subset_carrier.trans hT
  rcases FamilyStickyTubeParentDirectionCoherenceV1.Tube.endpoint_pairing_of_commonSegment
      (hundredTube W) T.axis haxis with hforward | hreverse
  · refine ⟨false, ?_, ?_⟩
    · have hraw := hforward.1
      have hdist : dist T.axis.base W.axis.base <= 300 * (delta : Real) := by
        have hraw' : dist W.axis.base T.axis.base <=
            3 * (100 * (delta : Real)) := by
          simpa [hundredRadius] using hraw
        rw [dist_comm]
        nlinarith
      simpa [dist_eq_norm] using hdist
    · have hgap :=
        direction_gap_le_two_mul_of_forward_endpoint_pairing
          W.axis T.axis hforward.1 hforward.2
      have hgap' : ‖T.axis.direction - W.axis.direction‖ <=
          2 * (3 * (100 * (delta : Real))) := by
        simpa [hundredRadius] using hgap
      have hgapFinal : ‖T.axis.direction - W.axis.direction‖ <=
          600 * (delta : Real) := by nlinarith
      simpa only [orientedLineParameter_false] using hgapFinal
  · refine ⟨true, ?_, ?_⟩
    · have hraw := hreverse.1
      have hdist : dist T.axis.endpoint W.axis.base <=
          300 * (delta : Real) := by
        have hraw' : dist W.axis.base T.axis.endpoint <=
            3 * (100 * (delta : Real)) := by
          simpa [hundredRadius] using hraw
        rw [dist_comm]
        nlinarith
      simpa [dist_eq_norm] using hdist
    · have hgap :=
        reverse_direction_gap_le_two_mul_of_reverse_endpoint_pairing
          W.axis T.axis hreverse.1 hreverse.2
      have hgap' : ‖-T.axis.direction - W.axis.direction‖ <=
          2 * (3 * (100 * (delta : Real))) := by
        simpa [hundredRadius] using hgap
      have hgapFinal : ‖-T.axis.direction - W.axis.direction‖ <=
          600 * (delta : Real) := by nlinarith
      simpa only [orientedLineParameter_true] using hgapFinal

/-- Product-coordinate form: one actual oriented parameter lies in the
`600 delta` ball about the container parameter. -/
theorem exists_orientation_parameter_near_hundredContainer
    {delta : NNReal} (T W : Tube delta)
    (hT : T.carrier ⊆ (hundredTube W).carrier) :
    exists e : Bool,
      ‖orientedLineParameter T e - containerLineParameter W‖ <=
        600 * (delta : Real) := by
  obtain ⟨e, hbase, hdir⟩ :=
    exists_orientation_componentwise_near_hundredContainer T W hT
  refine ⟨e, ?_⟩
  rw [Prod.norm_def]
  apply max_le
  · exact hbase.trans (by
      nlinarith [show 0 <= (delta : Real) by positivity])
  · exact hdir

/-- Data produced from two tubes sharing one literal container. -/
structure CommonContainerParameterData {delta : NNReal}
    (T U : Tube delta) where
  container : Tube delta
  T_subset : T.carrier ⊆ (hundredTube container).carrier
  U_subset : U.carrier ⊆ (hundredTube container).carrier
  T_orientation : Bool
  U_orientation : Bool
  T_near : ‖orientedLineParameter T T_orientation -
      containerLineParameter container‖ <= 600 * (delta : Real)
  U_near : ‖orientedLineParameter U U_orientation -
      containerLineParameter container‖ <= 600 * (delta : Real)

theorem CommonHundredContainer.parameterData
    {delta : NNReal} {T U : Tube delta}
    (h : CommonHundredContainer T U) :
    Nonempty (CommonContainerParameterData T U) := by
  obtain ⟨W, hT, hU⟩ := h
  obtain ⟨e, he⟩ :=
    exists_orientation_parameter_near_hundredContainer T W hT
  obtain ⟨f, hf⟩ :=
    exists_orientation_parameter_near_hundredContainer U W hU
  exact ⟨{
    container := W
    T_subset := hT
    U_subset := hU
    T_orientation := e
    U_orientation := f
    T_near := he
    U_near := hf }⟩

theorem CommonContainerParameterData.parameters_near
    {delta : NNReal} {T U : Tube delta}
    (D : CommonContainerParameterData T U) :
    ‖orientedLineParameter T D.T_orientation -
        orientedLineParameter U D.U_orientation‖ <=
      1200 * (delta : Real) := by
  calc
    ‖orientedLineParameter T D.T_orientation -
        orientedLineParameter U D.U_orientation‖ =
      ‖(orientedLineParameter T D.T_orientation -
          containerLineParameter D.container) +
        (containerLineParameter D.container -
          orientedLineParameter U D.U_orientation)‖ := by
        congr 1
        module
    _ <= ‖orientedLineParameter T D.T_orientation -
          containerLineParameter D.container‖ +
        ‖containerLineParameter D.container -
          orientedLineParameter U D.U_orientation‖ := norm_add_le _ _
    _ = ‖orientedLineParameter T D.T_orientation -
          containerLineParameter D.container‖ +
        ‖orientedLineParameter U D.U_orientation -
          containerLineParameter D.container‖ := by
      rw [norm_sub_rev (containerLineParameter D.container)
        (orientedLineParameter U D.U_orientation)]
    _ <= 1200 * (delta : Real) := by linarith [D.T_near, D.U_near]

/-- Every tube shares a `100` container with itself. -/
theorem commonHundredContainer_self {delta : NNReal} (T : Tube delta) :
    CommonHundredContainer T T :=
  ⟨T, carrier_subset_hundredTube T, carrier_subset_hundredTube T⟩

#print axioms direction_gap_le_two_mul_of_forward_endpoint_pairing
#print axioms reverse_direction_gap_le_two_mul_of_reverse_endpoint_pairing
#print axioms exists_orientation_componentwise_near_hundredContainer
#print axioms exists_orientation_parameter_near_hundredContainer
#print axioms CommonHundredContainer.parameterData
#print axioms CommonContainerParameterData.parameters_near
#print axioms commonHundredContainer_self

end
end FamilyStickyRandomWZLineParameterGeometryV1
