import FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
import FamilyStickyRandomFiniteFloorParameterNetV1
import Family6FiniteMapFiberCapCardV1

set_option autoImplicit false

open Set
open scoped NNReal Matrix

namespace FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyRandomFiniteFloorParameterNetV1
open Family6FiniteMapFiberCapCardV1

noncomputable section

/-!
# A full coefficient ball covered by half-scale active-centred balls

The reduced coefficient distance is the L1 distance in three real
coordinates.  Normalize one full-radius ball by its radius and encode the
three coordinates on a floor grid of mesh `1/6`.  Equal codes differ by
strictly less than one sixth in each coordinate, hence by less than one half
in L1.  There are at most `13^3 = 2197` codes.
-/

/-- The explicit dimension-only loss of the three-coordinate floor cover. -/
def actualHalfScaleCoefficientCoverLoss : Nat := 13 ^ 3

/-- Three normalized reduced coordinates relative to a fixed tube. -/
def normalizedActualReducedCoordinates
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (center : Tube delta)
    (deltaReal : Real) (i : iota) : Fin 3 -> Real :=
  ![(projectedTubeGraphA (fine.tubes i) - projectedTubeGraphA center) / deltaReal,
    (projectedTubeGraphB (fine.tubes i) - projectedTubeGraphB center) / deltaReal,
    (projectedTubeGraphD (fine.tubes i) - projectedTubeGraphD center) / deltaReal]

/-- A uniform cap for all active-centred half-radius coefficient balls gives
a full-radius cap with the explicit `13^3` covering loss. -/
theorem activeNearCoefficientIndices_card_le_full_of_half
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (hdelta : 0 < delta) {multiplicity : Nat}
    (hhalfCap : forall j, j ∈ active ->
      (activeNearCoefficientIndices fine active (fine.tubes j)
        ((delta : Real) / 2)).card <= multiplicity)
    (center : Tube delta) :
    (activeNearCoefficientIndices fine active center (delta : Real)).card <=
      actualHalfScaleCoefficientCoverLoss * multiplicity := by
  classical
  let d : Real := (delta : Real)
  have hd : 0 < d := by exact_mod_cast hdelta
  let source : Finset iota :=
    activeNearCoefficientIndices fine active center d
  let Parameter := {i // i ∈ source}
  let mesh : Real := 1 / 6
  have hmesh : 0 < mesh := by norm_num [mesh]
  let coord : Parameter -> Fin 3 -> Real := fun p =>
    normalizedActualReducedCoordinates fine center d p.1
  have hbound : forall p : Parameter, forall k : Fin 3,
      |coord p k| <= 1 := by
    intro p k
    have hpNear : projectedTubePairCoefficientDistance (fine.tubes p.1) center < d :=
      (Finset.mem_filter.mp p.2).2
    simp only [projectedTubePairCoefficientDistance, coefficientDistance,
      projectedTubePairDeltaA, projectedTubePairDeltaB, projectedTubePairDeltaD] at hpNear
    fin_cases k
    · change |(projectedTubeGraphA (fine.tubes p.1) - projectedTubeGraphA center) / d| <= 1
      rw [abs_div, abs_of_pos hd]
      apply (div_le_one hd).2
      linarith [abs_nonneg (projectedTubeGraphB (fine.tubes p.1) - projectedTubeGraphB center),
        abs_nonneg (projectedTubeGraphD (fine.tubes p.1) - projectedTubeGraphD center)]
    · change |(projectedTubeGraphB (fine.tubes p.1) - projectedTubeGraphB center) / d| <= 1
      rw [abs_div, abs_of_pos hd]
      apply (div_le_one hd).2
      linarith [abs_nonneg (projectedTubeGraphA (fine.tubes p.1) - projectedTubeGraphA center),
        abs_nonneg (projectedTubeGraphD (fine.tubes p.1) - projectedTubeGraphD center)]
    · change |(projectedTubeGraphD (fine.tubes p.1) - projectedTubeGraphD center) / d| <= 1
      rw [abs_div, abs_of_pos hd]
      apply (div_le_one hd).2
      linarith [abs_nonneg (projectedTubeGraphA (fine.tubes p.1) - projectedTubeGraphA center),
        abs_nonneg (projectedTubeGraphB (fine.tubes p.1) - projectedTubeGraphB center)]
  let Code := OccupiedCode mesh 1 hmesh coord hbound
  let code : Parameter -> Code :=
    ownCode mesh 1 hmesh coord hbound
  have hcodeFiber : forall c : Code,
      ((Finset.univ : Finset Parameter).filter fun p => code p = c).card <=
        multiplicity := by
    intro c
    let representativeParameter : Parameter :=
      representative mesh 1 hmesh coord hbound c
    let representativeIndex : iota := representativeParameter.1
    have hrepSource : representativeIndex ∈ source :=
      representativeParameter.2
    have hrepActive : representativeIndex ∈ active :=
      (Finset.mem_filter.mp hrepSource).1
    let fiber : Finset Parameter :=
      (Finset.univ : Finset Parameter).filter fun p => code p = c
    let halfFiber : Finset iota :=
      activeNearCoefficientIndices fine active
        (fine.tubes representativeIndex) (d / 2)
    have hclose : forall p : Parameter, p ∈ fiber ->
        projectedTubePairCoefficientDistance (fine.tubes p.1)
          (fine.tubes representativeIndex) < d / 2 := by
      intro p hp
      have hcode : code p = c := (Finset.mem_filter.mp hp).2
      have hcoordinate (k : Fin 3) :
          |coord p k - coord representativeParameter k| < mesh := by
        have h := abs_coord_sub_representative_ownCode_lt
          hmesh coord hbound p k
        change |coord p k - coord
          (representative mesh 1 hmesh coord hbound
            (ownCode mesh 1 hmesh coord hbound p)) k| < mesh at h
        change ownCode mesh 1 hmesh coord hbound p = c at hcode
        rw [hcode] at h
        exact h
      have hmeshMul : mesh * d = d / 6 := by
        dsimp only [mesh]
        ring
      have haNorm := hcoordinate 0
      have hbNorm := hcoordinate 1
      have hDNorm := hcoordinate 2
      have ha :
          |projectedTubeGraphA (fine.tubes p.1) -
            projectedTubeGraphA (fine.tubes representativeIndex)| < d / 6 := by
        change |(projectedTubeGraphA (fine.tubes p.1) - projectedTubeGraphA center) / d -
          (projectedTubeGraphA (fine.tubes representativeIndex) -
            projectedTubeGraphA center) / d| < mesh at haNorm
        have heq :
            (projectedTubeGraphA (fine.tubes p.1) - projectedTubeGraphA center) / d -
              (projectedTubeGraphA (fine.tubes representativeIndex) -
                projectedTubeGraphA center) / d =
              (projectedTubeGraphA (fine.tubes p.1) -
                projectedTubeGraphA (fine.tubes representativeIndex)) / d := by ring
        rw [heq, abs_div, abs_of_pos hd, div_lt_iff₀ hd] at haNorm
        rw [hmeshMul] at haNorm
        exact haNorm
      have hb :
          |projectedTubeGraphB (fine.tubes p.1) -
            projectedTubeGraphB (fine.tubes representativeIndex)| < d / 6 := by
        change |(projectedTubeGraphB (fine.tubes p.1) - projectedTubeGraphB center) / d -
          (projectedTubeGraphB (fine.tubes representativeIndex) -
            projectedTubeGraphB center) / d| < mesh at hbNorm
        have heq :
            (projectedTubeGraphB (fine.tubes p.1) - projectedTubeGraphB center) / d -
              (projectedTubeGraphB (fine.tubes representativeIndex) -
                projectedTubeGraphB center) / d =
              (projectedTubeGraphB (fine.tubes p.1) -
                projectedTubeGraphB (fine.tubes representativeIndex)) / d := by ring
        rw [heq, abs_div, abs_of_pos hd, div_lt_iff₀ hd] at hbNorm
        rw [hmeshMul] at hbNorm
        exact hbNorm
      have hD :
          |projectedTubeGraphD (fine.tubes p.1) -
            projectedTubeGraphD (fine.tubes representativeIndex)| < d / 6 := by
        change |(projectedTubeGraphD (fine.tubes p.1) - projectedTubeGraphD center) / d -
          (projectedTubeGraphD (fine.tubes representativeIndex) -
            projectedTubeGraphD center) / d| < mesh at hDNorm
        have heq :
            (projectedTubeGraphD (fine.tubes p.1) - projectedTubeGraphD center) / d -
              (projectedTubeGraphD (fine.tubes representativeIndex) -
                projectedTubeGraphD center) / d =
              (projectedTubeGraphD (fine.tubes p.1) -
                projectedTubeGraphD (fine.tubes representativeIndex)) / d := by ring
        rw [heq, abs_div, abs_of_pos hd, div_lt_iff₀ hd] at hDNorm
        rw [hmeshMul] at hDNorm
        exact hDNorm
      simp only [projectedTubePairCoefficientDistance, coefficientDistance,
        projectedTubePairDeltaA, projectedTubePairDeltaB, projectedTubePairDeltaD]
      linarith
    let embed : {p // p ∈ fiber} -> {i // i ∈ halfFiber} := fun p =>
      ⟨p.1.1, by
        change p.1.1 ∈ active.filter (fun i =>
          projectedTubePairCoefficientDistance (fine.tubes i)
            (fine.tubes representativeIndex) < d / 2)
        rw [Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp p.1.2).1,
          hclose p.1 p.2⟩⟩
    have hinjective : Function.Injective embed := by
      intro p q hpq
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : {i // i ∈ halfFiber} => x.1) hpq
    change fiber.card <= multiplicity
    calc
      fiber.card = Fintype.card {p // p ∈ fiber} :=
        (Fintype.card_coe fiber).symm
      _ <= Fintype.card {i // i ∈ halfFiber} :=
        Fintype.card_le_of_injective embed hinjective
      _ = halfFiber.card := Fintype.card_coe halfFiber
      _ <= multiplicity := by
        simpa only [halfFiber, d] using
          hhalfCap representativeIndex hrepActive
  have hsourceCode : source.card <= multiplicity * Fintype.card Code := by
    have hfinite := card_le_fiberCap_mul_card
      (Finset.univ : Finset Parameter) (Finset.univ : Finset Code)
      code multiplicity
      (fun _ _ => Finset.mem_univ _)
      (fun c _ => hcodeFiber c)
    calc
      source.card = Fintype.card Parameter := by
        change source.card = Fintype.card {i // i ∈ source}
        exact (Fintype.card_coe source).symm
      _ <= multiplicity * Fintype.card Code := by
        simpa only [Finset.card_univ] using hfinite
  have hcodeCard : Fintype.card Code <= actualHalfScaleCoefficientCoverLoss := by
    have h := card_occupiedCode_le mesh 1 hmesh coord hbound
    dsimp only [Code, actualHalfScaleCoefficientCoverLoss, mesh]
    norm_num [mesh, actualHalfScaleCoefficientCoverLoss] at h ⊢
    exact h
  change source.card <= actualHalfScaleCoefficientCoverLoss * multiplicity
  calc
    source.card <= multiplicity * Fintype.card Code := hsourceCode
    _ <= multiplicity * actualHalfScaleCoefficientCoverLoss :=
      Nat.mul_le_mul_left multiplicity hcodeCard
    _ = actualHalfScaleCoefficientCoverLoss * multiplicity := Nat.mul_comm _ _

#print axioms normalizedActualReducedCoordinates
#print axioms activeNearCoefficientIndices_card_le_full_of_half

end

end FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
