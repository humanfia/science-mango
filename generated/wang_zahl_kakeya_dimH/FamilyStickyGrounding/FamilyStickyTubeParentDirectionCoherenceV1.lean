import Submission.Kakeya.ConvexFactoring.MultiscaleTubeHierarchy

set_option autoImplicit false

open Set
open scoped NNReal

namespace FamilyStickyTubeParentDirectionCoherenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring

noncomputable section

/-!
# Unoriented direction coherence for actual tube parents

A tube axis is geometrically unoriented: reversing the unit direction and
swapping the endpoints gives the same segment.  Consequently the useful
notion of direction coherence is closeness either to the parent direction or
to its negative.  This file derives that closeness from the actual common
unit-segment witnesses already carried by `AdjacentTubeStep`; it does not add
an angle or aligned-box field to the hierarchy.
-/

/-- Two unit segments have directions within `eps`, up to reversal. -/
def UnorientedDirectionClose
    (S L : UnitSegment) (eps : Real) : Prop :=
  ‖S.direction - L.direction‖ <= eps ∨
    ‖S.direction + L.direction‖ <= eps

namespace UnorientedDirectionClose

/-- Unoriented direction closeness is symmetric. -/
theorem symm {S L : UnitSegment} {eps : Real}
    (h : UnorientedDirectionClose S L eps) :
    UnorientedDirectionClose L S eps := by
  rcases h with h | h
  · left
    calc
      ‖L.direction - S.direction‖ =
          ‖-(S.direction - L.direction)‖ := by congr 1; module
      _ = ‖S.direction - L.direction‖ := norm_neg _
      _ <= eps := h
  · right
    simpa [UnorientedDirectionClose, add_comm] using h

/-- Triangle inequality for unoriented directions. -/
theorem trans {S L P : UnitSegment} {eps eta : Real}
    (hSL : UnorientedDirectionClose S L eps)
    (hLP : UnorientedDirectionClose L P eta) :
    UnorientedDirectionClose S P (eps + eta) := by
  rcases hSL with hSL | hSL <;> rcases hLP with hLP | hLP
  · left
    calc
      ‖S.direction - P.direction‖ =
          ‖(S.direction - L.direction) +
            (L.direction - P.direction)‖ := by congr 1; module
      _ <= ‖S.direction - L.direction‖ +
          ‖L.direction - P.direction‖ := norm_add_le _ _
      _ <= eps + eta := add_le_add hSL hLP
  · right
    calc
      ‖S.direction + P.direction‖ =
          ‖(S.direction - L.direction) +
            (L.direction + P.direction)‖ := by congr 1; module
      _ <= ‖S.direction - L.direction‖ +
          ‖L.direction + P.direction‖ := norm_add_le _ _
      _ <= eps + eta := add_le_add hSL hLP
  · right
    calc
      ‖S.direction + P.direction‖ =
          ‖(S.direction + L.direction) -
            (L.direction - P.direction)‖ := by congr 1; module
      _ <= ‖S.direction + L.direction‖ +
          ‖L.direction - P.direction‖ := norm_sub_le _ _
      _ <= eps + eta := add_le_add hSL hLP
  · left
    calc
      ‖S.direction - P.direction‖ =
          ‖(S.direction + L.direction) -
            (L.direction + P.direction)‖ := by congr 1; module
      _ <= ‖S.direction + L.direction‖ +
          ‖L.direction + P.direction‖ := norm_sub_le _ _
      _ <= eps + eta := add_le_add hSL hLP

/-- A larger error bound preserves direction closeness. -/
theorem mono {S L : UnitSegment} {eps eta : Real}
    (h : UnorientedDirectionClose S L eps) (heps : eps <= eta) :
    UnorientedDirectionClose S L eta :=
  h.elim (fun hforward => Or.inl (hforward.trans heps))
    (fun hreverse => Or.inr (hreverse.trans heps))

end UnorientedDirectionClose

namespace Tube

/-- A common unit segment pairs the tube endpoints with the common endpoints,
possibly in reverse order, at cost `3r` per endpoint. -/
theorem endpoint_pairing_of_commonSegment
    {r : NNReal} (T : Tube r) (L : UnitSegment)
    (hL : L.carrier ⊆ T.carrier) :
    (dist T.axis.base L.base <= 3 * (r : Real) ∧
      dist T.axis.endpoint L.endpoint <= 3 * (r : Real)) ∨
    (dist T.axis.base L.endpoint <= 3 * (r : Real) ∧
      dist T.axis.endpoint L.base <= 3 * (r : Real)) := by
  obtain ⟨s0, hs0, hdist0⟩ :=
    T.exists_axis_parameter_dist_le_of_commonSegment L hL
      (t := 0) (by norm_num)
  obtain ⟨s1, hs1, hdist1⟩ :=
    T.exists_axis_parameter_dist_le_of_commonSegment L hL
      (t := 1) (by norm_num)
  have hsepRaw : (1 : Real) <= (r : Real) + |s0 - s1| + (r : Real) := by
    calc
      (1 : Real) = dist (L.point 0) (L.point 1) := by
        rw [L.dist_point_point]
        norm_num
      _ <= dist (L.point 0) (T.axis.point s0) +
            dist (T.axis.point s0) (T.axis.point s1) +
            dist (T.axis.point s1) (L.point 1) := dist_triangle4 _ _ _ _
      _ <= (r : Real) + |s0 - s1| + (r : Real) := by
        rw [T.axis.dist_point_point]
        exact add_le_add (add_le_add hdist0 le_rfl)
          (by simpa [dist_comm] using hdist1)
  have hsep : (1 : Real) - 2 * (r : Real) <= |s0 - s1| := by
    linarith
  rcases le_total s0 s1 with hs01 | hs10
  · left
    have habs : |s0 - s1| = s1 - s0 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hs01)]
      ring_nf
    have hs0Upper : s0 <= 2 * (r : Real) := by
      rw [habs] at hsep
      linarith [hs1.2]
    have hs1Lower : (1 : Real) - s1 <= 2 * (r : Real) := by
      rw [habs] at hsep
      linarith [hs0.1]
    constructor
    · calc
        dist T.axis.base L.base <=
            dist T.axis.base (T.axis.point s0) +
              dist (T.axis.point s0) L.base := dist_triangle _ _ _
        _ <= s0 + (r : Real) := by
          apply add_le_add
          · rw [← T.axis.point_zero, T.axis.dist_point_point]
            simp [abs_of_nonneg hs0.1]
          · simpa [L.point_zero, dist_comm] using hdist0
        _ <= 3 * (r : Real) := by linarith
    · calc
        dist T.axis.endpoint L.endpoint <=
            dist T.axis.endpoint (T.axis.point s1) +
              dist (T.axis.point s1) L.endpoint := dist_triangle _ _ _
        _ <= (1 - s1) + (r : Real) := by
          apply add_le_add
          · rw [← T.axis.point_one, T.axis.dist_point_point]
            simp [abs_of_nonneg (sub_nonneg.mpr hs1.2)]
          · simpa [L.point_one, dist_comm] using hdist1
        _ <= 3 * (r : Real) := by linarith
  · right
    have habs : |s0 - s1| = s0 - s1 :=
      abs_of_nonneg (sub_nonneg.mpr hs10)
    have hs1Upper : s1 <= 2 * (r : Real) := by
      rw [habs] at hsep
      linarith [hs0.2]
    have hs0Lower : (1 : Real) - s0 <= 2 * (r : Real) := by
      rw [habs] at hsep
      linarith [hs1.1]
    constructor
    · calc
        dist T.axis.base L.endpoint <=
            dist T.axis.base (T.axis.point s1) +
              dist (T.axis.point s1) L.endpoint := dist_triangle _ _ _
        _ <= s1 + (r : Real) := by
          apply add_le_add
          · rw [← T.axis.point_zero, T.axis.dist_point_point]
            simp [abs_of_nonneg hs1.1]
          · simpa [L.point_one, dist_comm] using hdist1
        _ <= 3 * (r : Real) := by linarith
    · calc
        dist T.axis.endpoint L.base <=
            dist T.axis.endpoint (T.axis.point s0) +
              dist (T.axis.point s0) L.base := dist_triangle _ _ _
        _ <= (1 - s0) + (r : Real) := by
          apply add_le_add
          · rw [← T.axis.point_one, T.axis.dist_point_point]
            simp [abs_of_nonneg (sub_nonneg.mpr hs0.2)]
          · simpa [L.point_zero, dist_comm] using hdist0
        _ <= 3 * (r : Real) := by linarith

/-- A unit segment contained in an `r`-tube has direction within `6r` of the
tube direction, up to reversal. -/
theorem unorientedDirectionClose_of_commonSegment
    {r : NNReal} (T : Tube r) (L : UnitSegment)
    (hL : L.carrier ⊆ T.carrier) :
    UnorientedDirectionClose T.axis L (6 * (r : Real)) := by
  rcases endpoint_pairing_of_commonSegment T L hL with h | h
  · left
    calc
      ‖T.axis.direction - L.direction‖ =
          ‖(T.axis.endpoint - L.endpoint) +
            (L.base - T.axis.base)‖ := by
              congr 1
              simp only [UnitSegment.endpoint]
              module
      _ <= ‖T.axis.endpoint - L.endpoint‖ +
          ‖L.base - T.axis.base‖ := norm_add_le _ _
      _ = dist T.axis.endpoint L.endpoint +
          dist L.base T.axis.base := by
            rw [dist_eq_norm, dist_eq_norm]
      _ = dist T.axis.endpoint L.endpoint +
          dist T.axis.base L.base := by rw [dist_comm L.base T.axis.base]
      _ <= 6 * (r : Real) := by linarith [h.1, h.2]
  · right
    calc
      ‖T.axis.direction + L.direction‖ =
          ‖(T.axis.endpoint - L.base) +
            (L.endpoint - T.axis.base)‖ := by
              congr 1
              simp only [UnitSegment.endpoint]
              module
      _ <= ‖T.axis.endpoint - L.base‖ +
          ‖L.endpoint - T.axis.base‖ := norm_add_le _ _
      _ = dist T.axis.endpoint L.base +
          dist L.endpoint T.axis.base := by
            rw [dist_eq_norm, dist_eq_norm]
      _ = dist T.axis.endpoint L.base +
          dist T.axis.base L.endpoint := by rw [dist_comm L.endpoint T.axis.base]
      _ <= 6 * (r : Real) := by linarith [h.1, h.2]

end Tube

namespace AdjacentTubeStep

variable {r R : NNReal} {ι κ : Type*}
  [DecidableEq ι] [DecidableEq κ]
  {child : Submission.Kakeya.Uniformity.UniformTubeFamily r ι}
  {parent : Submission.Kakeya.Uniformity.UniformTubeFamily R κ}

/-- The actual common-fine/partition witness at an adjacent hierarchy step
produces quantitative child-parent direction coherence. -/
theorem unorientedDirectionClose_parent
    (S : AdjacentTubeStep child parent) (i : ι)
    (hi : i ∈ S.combinatorics.index.fine) :
    UnorientedDirectionClose (child.tubes i).axis
      (parent.tubes (S.parentIndex i)).axis
      (6 * ((r : Real) + (R : Real))) := by
  cases S with
  | partition P =>
      have hcommon : (child.tubes i).axis.carrier ⊆
          (parent.tubes (P.index.parent i)).carrier :=
        (child.tubes i).axis_subset_carrier.trans (P.carrier_subset i hi)
      have hclose :=
        Tube.unorientedDirectionClose_of_commonSegment
          (parent.tubes (P.index.parent i)) (child.tubes i).axis hcommon
      apply UnorientedDirectionClose.mono
        (UnorientedDirectionClose.symm hclose)
      nlinarith [show 0 <= (r : Real) by positivity]
  | commonFine D =>
      obtain ⟨delta, fine, hFineChild, hFineParent⟩ := D.commonFine i hi
      have hChild :=
        Tube.unorientedDirectionClose_of_commonSegment (child.tubes i) fine.axis
          (fine.axis_subset_carrier.trans hFineChild)
      have hParent :=
        Tube.unorientedDirectionClose_of_commonSegment
          (parent.tubes (D.combinatorics.index.parent i)) fine.axis
          (fine.axis_subset_carrier.trans hFineParent)
      apply UnorientedDirectionClose.mono
        (UnorientedDirectionClose.trans hChild
          (UnorientedDirectionClose.symm hParent))
      show 6 * (r : Real) + 6 * (R : Real) <=
        6 * ((r : Real) + (R : Real))
      ring_nf
      exact le_rfl

end AdjacentTubeStep

namespace MultiscaleTubeHierarchy

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*} [∀ l, DecidableEq (Index l)]

/-- Direction coherence at one actual hierarchy edge.  Recursive buffering
does not change either axis, so the same bound applies to effective tubes. -/
theorem effective_unorientedDirectionClose_parent
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (l : Nat) (hl : l < depth) (i : Index l)
    (hi : i ∈ (H.family l).refinement.refined) :
    UnorientedDirectionClose ((H.effectiveFamily l).tubes i).axis
      ((H.effectiveFamily (l + 1)).tubes
        ((H.step l hl).parentIndex i)).axis
      (6 * ((nominalRadius l : Real) +
        (nominalRadius (l + 1) : Real))) := by
  have hi' : i ∈ (H.step l hl).combinatorics.index.fine := by
    rw [(H.step l hl).combinatorics.fine_eq_refined]
    exact hi
  simpa [MultiscaleTubeHierarchy.effectiveFamily,
    Submission.Kakeya.Uniformity.UniformTubeFamily.buffer] using
      AdjacentTubeStep.unorientedDirectionClose_parent (H.step l hl) i hi'

end MultiscaleTubeHierarchy

#print axioms Tube.endpoint_pairing_of_commonSegment
#print axioms Tube.unorientedDirectionClose_of_commonSegment
#print axioms AdjacentTubeStep.unorientedDirectionClose_parent
#print axioms MultiscaleTubeHierarchy.effective_unorientedDirectionClose_parent

end
end FamilyStickyTubeParentDirectionCoherenceV1
