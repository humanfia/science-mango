import Family6Grounding.Family6CanonicalFrostmanConstantCoreV1
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

/-!
# Relative cardinality cap from one literal Family7 graph

Katz--Tao control of a graph of radius-`tau` tubes is tested on the actual
radius-`rho` parent containing that graph.  The standard lower fine-tube and
upper parent-tube volume bounds then give the sharp relative-square count
bound.  No whole-cover Katz--Tao hypothesis or replacement graph is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GraphKatzTaoRelativeCardCapV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1

noncomputable section

variable {tau rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-- A literal Katz--Tao graph contained in one actual parent has cardinality
at most `16 C (rho / tau)^2`. -/
theorem graph_card_le_sixteen_mul_katzTao_mul_relativeSquare
    (F : UniformTubeFamily tau iota) (graph : Finset iota)
    (parent : Tube rho)
    (htau : 0 < tau)
    (htauHalf : tau ≤ (2 : NNReal)⁻¹)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hcontained : ∀ i, i ∈ graph →
      (F.tubes i).carrier ⊆ parent.carrier)
    {C : ENNReal}
    (hKT : IsKatzTao C (activeSubtypeFamily F.bodyFamily graph)) :
    (graph.card : ENNReal) ≤
      16 * C * (((rho / tau : NNReal) : ENNReal) ^ 2) := by
  let G := activeSubtypeFamily F.bodyFamily graph
  let floor : ENNReal := (tau : ENNReal) ^ 2 / 2
  have hfamilyLower : (graph.card : ENNReal) * floor ≤ familyVolume G := by
    unfold familyVolume G activeSubtypeFamily
    simp only [UniformTubeFamily.bodyFamily, Tube.coe_body]
    calc
      (graph.card : ENNReal) * floor =
          ∑ _i : {i // i ∈ graph}, floor := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_coe]
      _ ≤ ∑ i : {i // i ∈ graph},
          volume (F.tubes i.1).carrier := by
        exact Finset.sum_le_sum fun i _ =>
          (F.tubes i.1).half_sq_le_volume_of_le_half htauHalf
  have hfamilyContained : ∀ i,
      (G i : Set Space) ⊆ (parent.body : Set Space) := by
    intro i
    change (F.tubes i.1).carrier ⊆ parent.carrier
    exact hcontained i.1 i.2
  have hmass : containedMass G parent.body = familyVolume G :=
    containedMass_eq_familyVolume_of_contained G parent.body hfamilyContained
  have hKTParent : familyVolume G ≤
      C * volume (parent.body : Set Space) := by
    have h := hKT parent.body
    unfold IsKatzTaoAt at h
    rw [hmass] at h
    exact h
  have hparentUpper : volume (parent.body : Set Space) ≤
      8 * (rho : ENNReal) ^ 2 := by
    simpa only [Tube.coe_body] using
      parent.volume_le_eight_mul_sq_of_le_half hrhoHalf
  have hscaled : (graph.card : ENNReal) * floor ≤
      C * (8 * (rho : ENNReal) ^ 2) := by
    exact hfamilyLower.trans <| hKTParent.trans <|
      mul_le_mul' le_rfl hparentUpper
  have hratioNN :
      (rho / tau) ^ (2 : Nat) * (tau ^ (2 : Nat) / 2) =
        rho ^ (2 : Nat) / 2 := by
    field_simp [htau.ne']
  have hratio :
      (((rho / tau : NNReal) : ENNReal) ^ 2) * floor =
        (rho : ENNReal) ^ 2 / 2 := by
    have hcast := congrArg (fun x : NNReal => (x : ENNReal)) hratioNN
    simpa only [floor, ENNReal.coe_mul, ENNReal.coe_div htau.ne',
      ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
      ENNReal.coe_pow, ENNReal.coe_ofNat] using hcast
  have hsixteen : (16 : ENNReal) * (2 : ENNReal)⁻¹ = 8 := by
    calc
      (16 : ENNReal) * (2 : ENNReal)⁻¹ =
          (8 * 2) * (2 : ENNReal)⁻¹ := by norm_num
      _ = 8 * (2 * (2 : ENNReal)⁻¹) := by ac_rfl
      _ = 8 * 1 := by
        rw [ENNReal.mul_inv_cancel] <;> norm_num
      _ = 8 := mul_one _
  have hcoefficient :
      (16 * C * (((rho / tau : NNReal) : ENNReal) ^ 2)) * floor =
        C * (8 * (rho : ENNReal) ^ 2) := by
    calc
      (16 * C * (((rho / tau : NNReal) : ENNReal) ^ 2)) * floor =
          (16 * C) *
            ((((rho / tau : NNReal) : ENNReal) ^ 2) * floor) := by
        ac_rfl
      _ = (16 * C) * ((rho : ENNReal) ^ 2 / 2) := by rw [hratio]
      _ = C * (8 * (rho : ENNReal) ^ 2) := by
        rw [div_eq_mul_inv]
        calc
          (16 * C) * ((rho : ENNReal) ^ 2 * (2 : ENNReal)⁻¹) =
              C * (rho : ENNReal) ^ 2 *
                (16 * (2 : ENNReal)⁻¹) := by ring
          _ = C * (rho : ENNReal) ^ 2 * 8 := by rw [hsixteen]
          _ = C * (8 * (rho : ENNReal) ^ 2) := by ring
  have htau0 : (tau : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr htau.ne'
  have hfloor0 : floor ≠ 0 := by
    dsimp only [floor]
    exact ENNReal.div_ne_zero.mpr
      ⟨pow_ne_zero 2 htau0, by norm_num⟩
  have hfloorTop : floor ≠ ∞ := by
    dsimp only [floor]
    exact ENNReal.div_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num)
  apply (ENNReal.mul_le_mul_iff_right hfloor0 hfloorTop).mp
  simpa only [mul_comm] using
    (show (graph.card : ENNReal) * floor ≤
        (16 * C * (((rho / tau : NNReal) : ENNReal) ^ 2)) * floor from
      hscaled.trans_eq hcoefficient.symm)

/-- Every finite selection indexed by that literal graph satisfies the same
relative-square cap. -/
theorem selectedGraphSubtype_card_le_sixteen_mul_katzTao_mul_relativeSquare
    (F : UniformTubeFamily tau iota) (graph : Finset iota)
    (selected : Finset {i // i ∈ graph})
    (parent : Tube rho)
    (htau : 0 < tau)
    (htauHalf : tau ≤ (2 : NNReal)⁻¹)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hcontained : ∀ i, i ∈ graph →
      (F.tubes i).carrier ⊆ parent.carrier)
    {C : ENNReal}
    (hKT : IsKatzTao C (activeSubtypeFamily F.bodyFamily graph)) :
    (selected.card : ENNReal) ≤
      16 * C * (((rho / tau : NNReal) : ENNReal) ^ 2) := by
  calc
    (selected.card : ENNReal) ≤ (graph.card : ENNReal) := by
      have hcard :
          selected.card ≤ Fintype.card {i // i ∈ graph} :=
        Finset.card_le_univ selected
      rw [Fintype.card_coe] at hcard
      exact_mod_cast hcard
    _ ≤ 16 * C * (((rho / tau : NNReal) : ENNReal) ^ 2) :=
      graph_card_le_sixteen_mul_katzTao_mul_relativeSquare
        F graph parent htau htauHalf hrhoHalf hcontained hKT

#print axioms graph_card_le_sixteen_mul_katzTao_mul_relativeSquare
#print axioms
  selectedGraphSubtype_card_le_sixteen_mul_katzTao_mul_relativeSquare

end
end Family8Family7GraphKatzTaoRelativeCardCapV3
