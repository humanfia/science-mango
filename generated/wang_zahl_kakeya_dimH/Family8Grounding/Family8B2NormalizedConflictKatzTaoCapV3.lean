import Family8Grounding.Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV3
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8B2NormalizedConflictKatzTaoCapV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
open Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV3

noncomputable section

/-!
# Katz--Tao degree cap for the literal B2 normalized conflict graph

Every tube conflicting with one fixed eighth-normalized anchor lies in the
anchor's honest elongated paper body.  Its volume is bounded below at the
same normalized radius, while the body's volume is exactly proportional to
that radius squared.  Thus global Katz--Tao control of the literal normalized
datum gives a finite, callback-free cap for `normalizedConflictIndices`.
-/

/-- The exact natural ceiling furnished by the elongated-body mass ratio. -/
def normalizedConflictKatzTaoNatCap
    (delta : NNReal) (A : ENNReal) : Nat :=
  Nat.ceil
    ((A * ((240000 : ENNReal) * ((delta / 8 : NNReal) : ENNReal) ^ 2) /
      (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)).toReal)

/-- Katz--Tao mass controls the literal conflict set of every anchor in the
eighth-normalized datum. -/
theorem normalizedConflictIndices_card_mul_halfSq_le_katzTao_elongated
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    {A : ENNReal}
    (hKT : IsKatzTao A (eighthNormalizedDatum D).family.bodyFamily)
    (a : iota) :
    ((normalizedConflictIndices D a).card : ENNReal) *
        (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) <=
      A * ((240000 : ENNReal) *
        ((delta / 8 : NNReal) : ENNReal) ^ 2) := by
  classical
  let T : Tube (delta / 8) :=
    (eighthNormalizedDatum D).family.tubes a
  obtain ⟨frame, hframe⟩ := T.exists_alignedFrame
  let K : ConvexBody Space := paperElongatedBody T frame
  have hrhoPos : 0 < delta / 8 := div_pos hdeltaPos (by norm_num)
  have hrhoSmall : delta / 8 <= (1 / 16 : NNReal) := by
    rw [← NNReal.coe_le_coe]
    have hreal' : (delta : Real) <= (((2 : NNReal)⁻¹ : NNReal) : Real) :=
      NNReal.coe_le_coe.mpr hdeltaHalf
    have hreal : (delta : Real) <= (1 / 2 : Real) := by
      simpa using hreal'
    push_cast
    linarith
  have hsubset : normalizedConflictIndices D a ⊆
      containedIndices (eighthNormalizedDatum D).family.bodyFamily K := by
    intro b hb
    rw [normalizedConflictIndices, Finset.mem_filter] at hb
    rw [mem_containedIndices]
    let U : Tube (delta / 8) :=
      (eighthNormalizedDatum D).family.tubes b
    have hconflict : ¬ EssentiallyDistinct T U := by
      intro hTU
      exact hb.2 ((essentiallyDistinct_comm T U).mp hTU)
    exact carrier_subset_paperElongatedBody_of_not_essentiallyDistinct
      T U frame hframe hrhoPos hrhoSmall hconflict
  have hrhoHalf : delta / 8 <= (2 : NNReal)⁻¹ := by
    exact (div_le_self (show 0 <= delta from bot_le)
      (by norm_num : (1 : NNReal) <= 8)).trans hdeltaHalf
  have hlower :
      ((normalizedConflictIndices D a).card : ENNReal) *
          (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) <=
        containedMass (eighthNormalizedDatum D).family.bodyFamily K := by
    calc
      ((normalizedConflictIndices D a).card : ENNReal) *
          (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) =
          ∑ _b ∈ normalizedConflictIndices D a,
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) := by
              simp [nsmul_eq_mul]
      _ <= ∑ b ∈ normalizedConflictIndices D a,
          volume ((eighthNormalizedDatum D).family.tubes b).carrier := by
        apply Finset.sum_le_sum
        intro b _hb
        exact ((eighthNormalizedDatum D).family.tubes b).half_sq_le_volume_of_le_half
          hrhoHalf
      _ <= ∑ b ∈
          containedIndices (eighthNormalizedDatum D).family.bodyFamily K,
          volume ((eighthNormalizedDatum D).family.tubes b).carrier := by
        exact Finset.sum_le_sum_of_subset hsubset
      _ = containedMass
          (eighthNormalizedDatum D).family.bodyFamily K := by rfl
  calc
    ((normalizedConflictIndices D a).card : ENNReal) *
        (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) <=
        containedMass (eighthNormalizedDatum D).family.bodyFamily K := hlower
    _ <= A * volume (K : Set Space) := hKT K
    _ = A * ((240000 : ENNReal) *
        ((delta / 8 : NNReal) : ENNReal) ^ 2) := by
      rw [volume_paperElongatedBody]

/-- Natural-cardinality form of the same-datum normalized conflict cap. -/
theorem normalizedConflictIndices_card_le_katzTaoNatCap
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    {A : ENNReal} (hAfinite : A ≠ ∞)
    (hKT : IsKatzTao A (eighthNormalizedDatum D).family.bodyFamily)
    (a : iota) :
    (normalizedConflictIndices D a).card <=
      normalizedConflictKatzTaoNatCap delta A := by
  let floor : ENNReal :=
    ((delta / 8 : NNReal) : ENNReal) ^ 2 / 2
  let total : ENNReal :=
    A * ((240000 : ENNReal) *
      ((delta / 8 : NNReal) : ENNReal) ^ 2)
  have hrhoPos : 0 < delta / 8 := div_pos hdeltaPos (by norm_num)
  have hfloor0 : floor ≠ 0 := by
    dsimp only [floor]
    exact ENNReal.div_ne_zero.mpr
      ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hrhoPos.ne'), by norm_num⟩
  have hfloorTop : floor ≠ ∞ := by
    dsimp only [floor]
    exact ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (by norm_num)
  have htotalTop : total ≠ ∞ := by
    dsimp only [total]
    apply ENNReal.mul_ne_top hAfinite
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hquotientTop : total / floor ≠ ∞ :=
    ENNReal.div_ne_top htotalTop hfloor0
  have hcross :=
    normalizedConflictIndices_card_mul_halfSq_le_katzTao_elongated
      D hdeltaPos hdeltaHalf hKT a
  have hquotient :
      ((normalizedConflictIndices D a).card : ENNReal) <=
        total / floor := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hfloor0) (Or.inl hfloorTop)).2
    simpa only [total, floor] using hcross
  have hreal : ((normalizedConflictIndices D a).card : Real) <=
      (total / floor).toReal := by
    have h := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top
      hquotientTop).2 hquotient
    simpa using h
  have hceil : ((normalizedConflictIndices D a).card : Real) <=
      (Nat.ceil ((total / floor).toReal) : Real) :=
    hreal.trans (Nat.le_ceil _)
  change (normalizedConflictIndices D a).card <=
    Nat.ceil ((total / floor).toReal)
  exact_mod_cast hceil

/-- Raw source Katz--Tao control automatically supplies the normalized cap,
including the honest fixed normalization loss `128`. -/
theorem normalizedConflictIndices_card_le_sourceKatzTaoNatCap
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (a : iota) :
    (normalizedConflictIndices D a).card <=
      normalizedConflictKatzTaoNatCap delta (128 * C) := by
  apply normalizedConflictIndices_card_le_katzTaoNatCap
    D hdeltaPos hdeltaHalf
  · exact ENNReal.mul_ne_top (by norm_num) hCfinite
  · exact eighthNormalizedDatum_isKatzTao D hdeltaHalf hKT

#print axioms normalizedConflictIndices_card_mul_halfSq_le_katzTao_elongated
#print axioms normalizedConflictIndices_card_le_katzTaoNatCap
#print axioms normalizedConflictIndices_card_le_sourceKatzTaoNatCap

end
end Family8B2NormalizedConflictKatzTaoCapV3
