import Family8Grounding.Family8Family7NativeHighAmbientCardPowerV1
import Family8Grounding.Family8CommonPointTubePackingV1
import Family8Grounding.Family8SphereDirectionPackingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighAmbientPackingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8CommonPointTubePackingV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyRandomFiniteFloorParameterNetV1

noncomputable section

universe u

/-!
# Global packing of the genuine extremal ambient family

Unlike `NativeBranchCore`, the upstream epsilon-extremal datum retains two
geometric facts: all active tube carriers lie in the unit ball and the active
family is pairwise essentially distinct.  A three-coordinate midpoint grid
and the existing two-coordinate sphere packing give a completely explicit
polynomial ambient-cardinality cap.  No branch conclusion is assumed.
-/

/-- Midpoint coordinates used by the global unit-ball packing. -/
def nativeHighAmbientPositionCoordinates {delta : NNReal}
    (T : Tube delta) : Fin 3 -> Real :=
  fun k => (tubeAxisMidpoint T) k

/-- Position mesh at which equal codes force the overlap-scale midpoint
closeness. -/
def nativeHighAmbientPositionMesh (delta : NNReal) : Real :=
  (delta : Real) / 1000

def nativeHighAmbientPositionBound : Real := 1

/-- Number of possible midpoint grid cells inside the unit ball. -/
def nativeHighAmbientPositionCodeCap (delta : NNReal) : Nat :=
  ((Int.floor
        (nativeHighAmbientPositionBound /
          nativeHighAmbientPositionMesh delta) + 1 -
      Int.floor
        (-nativeHighAmbientPositionBound /
          nativeHighAmbientPositionMesh delta)).toNat) ^ 3

/-- Explicit five-parameter global tube-packing cap. -/
def nativeHighAmbientPackingNatCap (delta : NNReal) : Nat :=
  nativeHighAmbientPositionCodeCap delta * commonPointDirectionCap delta

/-- Unit-ball support bounds every midpoint coordinate by one. -/
theorem abs_nativeHighAmbientPositionCoordinates_le_one
    {delta : NNReal} {index : Type u} [DecidableEq index]
    (tube : index -> Tube delta) {i : index}
    (hcontained : (tube i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (k : Fin 3) :
    |nativeHighAmbientPositionCoordinates (tube i) k| <=
      nativeHighAmbientPositionBound := by
  have hmidCarrier : tubeAxisMidpoint (tube i) ∈ (tube i).carrier := by
    apply (tube i).axis_subset_carrier
    exact (tube i).axis.mem_carrier_of_mem_Icc (by norm_num)
  have hmidBall := hcontained hmidCarrier
  have hnorm : ‖tubeAxisMidpoint (tube i)‖ <= 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hmidBall
  exact (abs_apply_le_norm (tubeAxisMidpoint (tube i)) k).trans hnorm

/-- Equal midpoint grid codes imply the quantitative midpoint closeness used
by the existing essential-distinctness contradiction. -/
theorem midpoint_close_of_nativeHighAmbient_floorCode_eq
    {delta : NNReal} (hdeltaPos : 0 < delta) (T U : Tube delta)
    (hcode :
      floorCode (nativeHighAmbientPositionMesh delta)
          nativeHighAmbientPositionCoordinates T =
        floorCode (nativeHighAmbientPositionMesh delta)
          nativeHighAmbientPositionCoordinates U) :
    dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) <=
      (delta : Real) / 100 := by
  apply dist_le_delta_div_hundred_of_coordinate_close
  intro k
  have hmesh : 0 < nativeHighAmbientPositionMesh delta := by
    exact div_pos (NNReal.coe_pos.mpr hdeltaPos) (by norm_num)
  have hk := abs_coord_sub_lt_of_floorCode_eq hmesh
    nativeHighAmbientPositionCoordinates hcode k
  simpa only [nativeHighAmbientPositionCoordinates,
    nativeHighAmbientPositionMesh] using hk

/-- Any essentially-distinct finite family whose carriers are contained in
the unit ball has at most the explicit global packing cap many members. -/
theorem card_le_nativeHighAmbientPackingNatCap
    {delta : NNReal} {index : Type u} [DecidableEq index]
    (indices : Finset index) (tube : index -> Tube delta)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta <= (1 / 100 : NNReal))
    (hcontained : forall i, i ∈ indices ->
      (tube i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hpairwise : Set.Pairwise (indices : Set index) fun i j =>
      EssentiallyDistinct (tube i) (tube j)) :
    indices.card <= nativeHighAmbientPackingNatCap delta := by
  classical
  let Parameter := ↥indices
  let mesh : Real := nativeHighAmbientPositionMesh delta
  let bound : Real := nativeHighAmbientPositionBound
  let coord : Parameter -> Fin 3 -> Real := fun p =>
    nativeHighAmbientPositionCoordinates (tube p.1)
  have hmesh : 0 < mesh := by
    exact div_pos (NNReal.coe_pos.mpr hdeltaPos) (by norm_num)
  have hbound : forall p : Parameter, forall k, |coord p k| <= bound := by
    intro p k
    simpa only [coord, bound] using
      abs_nativeHighAmbientPositionCoordinates_le_one tube
        (hcontained p.1 p.property) k
  let Code := OccupiedCode mesh bound hmesh coord hbound
  let code : Parameter -> Code := fun p =>
    ownCode mesh bound hmesh coord hbound p
  have hscalePos : 0 < delta / 100 := div_pos hdeltaPos (by norm_num)
  have hscaleOne : delta / 100 <= (1 : NNReal) := by
    apply (div_le_one (by norm_num : (0 : NNReal) < 100)).2
    exact hdeltaSmall.trans (by
      exact_mod_cast (show (1 : Real) / 100 <= 100 by norm_num))
  have hfiber : ∀ c ∈ (Finset.univ : Finset Code),
      ((Finset.univ : Finset Parameter).filter fun p => code p = c).card <=
        commonPointDirectionCap delta := by
    intro c _hc
    let fiber : Finset Parameter :=
      (Finset.univ : Finset Parameter).filter fun p => code p = c
    have hseparated : ∀ p ∈ fiber, ∀ q ∈ fiber, p ≠ q →
        (((delta / 100 : NNReal) : Real)) <=
          dist (tube p.1).axis.direction (tube q.1).axis.direction := by
      intro p hp q hq hpq
      have hpFilter := Finset.mem_filter.mp hp
      have hqFilter := Finset.mem_filter.mp hq
      have hpqVal : p.1 ≠ q.1 := by
        intro hpqVal
        apply hpq
        exact Subtype.ext hpqVal
      have hcodeEq : code p = code q := hpFilter.2.trans hqFilter.2.symm
      have hboundedEq :
          FamilyStickyRandomFiniteFloorParameterNetV1.boundedFloorCode
              mesh bound hmesh coord hbound p =
            FamilyStickyRandomFiniteFloorParameterNetV1.boundedFloorCode
              mesh bound hmesh coord hbound q :=
        congrArg Subtype.val hcodeEq
      have hfloorEq :
          FamilyStickyRandomFiniteFloorParameterNetV1.floorCode mesh coord p =
            FamilyStickyRandomFiniteFloorParameterNetV1.floorCode mesh coord q := by
        funext k
        exact congrArg Subtype.val (congrFun hboundedEq k)
      have hfloorTube :
          FamilyStickyRandomFiniteFloorParameterNetV1.floorCode
              (nativeHighAmbientPositionMesh delta)
              nativeHighAmbientPositionCoordinates (tube p.1) =
            FamilyStickyRandomFiniteFloorParameterNetV1.floorCode
              (nativeHighAmbientPositionMesh delta)
              nativeHighAmbientPositionCoordinates (tube q.1) := by
        funext k
        have hk := congrFun hfloorEq k
        change Int.floor
            (nativeHighAmbientPositionCoordinates (tube p.1) k /
              nativeHighAmbientPositionMesh delta) =
          Int.floor
            (nativeHighAmbientPositionCoordinates (tube q.1) k /
              nativeHighAmbientPositionMesh delta)
        change Int.floor
            (nativeHighAmbientPositionCoordinates (tube p.1) k /
              nativeHighAmbientPositionMesh delta) =
          Int.floor
            (nativeHighAmbientPositionCoordinates (tube q.1) k /
              nativeHighAmbientPositionMesh delta) at hk
        exact hk
      have hmid := midpoint_close_of_nativeHighAmbient_floorCode_eq
        hdeltaPos (tube p.1) (tube q.1) hfloorTube
      have hessential := hpairwise p.property q.property hpqVal
      by_contra hnotSeparated
      have hdirection :
          dist (tube p.1).axis.direction (tube q.1).axis.direction <=
            (delta : Real) / 100 := by
        have hlt := (lt_of_not_ge hnotSeparated).le
        norm_num at hlt ⊢
        exact hlt
      obtain ⟨frame, hframe⟩ := (tube p.1).exists_alignedFrame
      exact (not_essentiallyDistinct_of_midpoint_direction_close
        (tube p.1) (tube q.1) frame hframe hdeltaPos hdeltaSmall
        hmid hdirection) hessential
    let directions : Finset Space :=
      fiber.image fun p => (tube p.1).axis.direction
    have hdirectionsCard : directions.card = fiber.card := by
      apply Finset.card_image_iff.mpr
      intro p hp q hq hdirection
      by_contra hpq
      have hsep := hseparated p hp q hq hpq
      change (tube p.1).axis.direction = (tube q.1).axis.direction at hdirection
      rw [hdirection, dist_self] at hsep
      exact (not_le_of_gt (NNReal.coe_pos.mpr hscalePos)) hsep
    have hcard :=
      Family8SphereDirectionPackingV1.directionFinset_card_le_natCeil_thirtyTwo_mul_inv_sq
        directions id (delta / 100) hscalePos hscaleOne (by
          intro direction hdirection
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hdirection
          exact (tube p.1).axis.norm_direction) (by
          intro direction hdirection direction' hdirection' hne
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hdirection
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hdirection'
          apply hseparated p hp q hq
          intro hpq
          apply hne
          subst q
          rfl)
    rw [← hdirectionsCard]
    simpa only [directions, commonPointDirectionCap] using hcard
  have hfinite := Family6FiniteMapFiberCapCardV1.card_le_fiberCap_mul_card
    (Finset.univ : Finset Parameter) (Finset.univ : Finset Code) code
    (commonPointDirectionCap delta) (by simp) hfiber
  have hcodeCard : Fintype.card Code <=
      nativeHighAmbientPositionCodeCap delta := by
    have h := card_occupiedCode_le mesh bound hmesh coord hbound
    simpa only [Code, mesh, bound, nativeHighAmbientPositionCodeCap,
      Fintype.card_fin] using h
  calc
    indices.card = Fintype.card Parameter := by
      simp only [Parameter, Fintype.card_coe]
    _ <= commonPointDirectionCap delta * Fintype.card Code := by
      simpa only [Finset.card_univ] using hfinite
    _ <= commonPointDirectionCap delta *
        nativeHighAmbientPositionCodeCap delta := by
      exact Nat.mul_le_mul_left _ hcodeCard
    _ = nativeHighAmbientPackingNatCap delta := by
      simp only [nativeHighAmbientPackingNatCap, Nat.mul_comm]

/-- The genuine upstream extremal record automatically supplies every
hypothesis of the global ambient packing theorem. -/
theorem extremalAmbient_card_le_nativeHighAmbientPackingNatCap
    {delta : NNReal} {index : Type u} [Fintype index] [DecidableEq index]
    (S : WZL3UniformTubeSource delta index) (ambient : Finset index)
    {Y : Shading S.family.bodyFamily} {parallelLoss : Nat}
    {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily S.family Y ambient parallelLoss
      epsilon sigma)
    (hdeltaSmall : delta <= (1 / 100 : NNReal)) :
    ambient.card <= nativeHighAmbientPackingNatCap delta := by
  exact card_le_nativeHighAmbientPackingNatCap ambient S.family.tubes
    G.delta_pos hdeltaSmall G.contained_in_unit_ball G.essentially_distinct

#print axioms nativeHighAmbientPositionCoordinates
#print axioms nativeHighAmbientPackingNatCap
#print axioms abs_nativeHighAmbientPositionCoordinates_le_one
#print axioms midpoint_close_of_nativeHighAmbient_floorCode_eq
#print axioms card_le_nativeHighAmbientPackingNatCap
#print axioms extremalAmbient_card_le_nativeHighAmbientPackingNatCap

end
end Family8Family7NativeHighAmbientPackingV1
