import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

/-!
# A fibre Frostman bound forces parent card--scale mass, V3

V1 and V2 were elaboration drafts and are not imported.  This successor
records explicitly that the active-subtype family and the literal Sticky
fibre family are the same function before transporting family volume.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyFiberFrostmanParentCardScaleV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- A nonempty fibre Frostman certificate controls the actual parent volume
by the multiplicity-counted body mass of that same literal fibre. -/
theorem parentVolume_le_frostman_mul_fiberFamilyVolume
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta)
    (k : Fin S.coarseCard) (hk : (S.fiber k).Nonempty)
    {C : ENNReal}
    (hF : IsFrostmanOn C fine.bodyFamily (S.fiber k)
      (S.coarse.tubes k).body) :
    volume (S.coarse.tubes k).carrier <=
      C * familyVolume (S.fiberFamily k) := by
  let Fk := activeSubtypeFamily fine.bodyFamily (S.fiber k)
  let K := (S.coarse.tubes k).body
  have hFin : IsFrostmanIn C Fk K := by
    exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      fine.bodyFamily (S.fiber k) (S.coarse.tubes k).body).mp hF
  obtain ⟨i, hi⟩ := hk
  let ii : {i // i ∈ S.fiber k} := ⟨i, hi⟩
  let Kprime : ConvexBody Space := Fk ii
  have hsubset : (Kprime : Set Space) ⊆ (K : Set Space) :=
    hFin.family_subset ii
  have htubeMass : volume (Kprime : Set Space) ≤
      containedMass Fk Kprime := by
    unfold containedMass
    exact Finset.single_le_sum
      (fun j _ => show
        (0 : ENNReal) ≤ volume (Fk j : Set Space) from bot_le)
      ((mem_containedIndices Fk Kprime ii).2 subset_rfl)
  have hindices : containedIndices Fk K = Finset.univ := by
    ext j
    simp only [mem_containedIndices, Finset.mem_univ, iff_true]
    exact hFin.family_subset j
  have hambient : containedMass Fk K = familyVolume Fk := by
    unfold containedMass familyVolume
    rw [hindices]
  have hcross := IsFrostmanIn.cross_le hFin hsubset
  rw [hambient] at hcross
  have hchain : volume (Kprime : Set Space) * volume (K : Set Space) ≤
      (C * familyVolume Fk) * volume (Kprime : Set Space) := by
    calc
      volume (Kprime : Set Space) * volume (K : Set Space) ≤
          containedMass Fk Kprime * volume (K : Set Space) :=
        mul_le_mul_left htubeMass _
      _ ≤ (C * familyVolume Fk) * volume (Kprime : Set Space) := hcross
  have htube0 : volume (Kprime : Set Space) ≠ 0 := by
    change volume (fine.tubes i).carrier ≠ 0
    exact (fine.tubes i).volume_pos hdelta |>.ne'
  have htubeTop : volume (Kprime : Set Space) ≠ ∞ := by
    change volume (fine.tubes i).carrier ≠ ∞
    exact (fine.tubes i).volume_lt_top.ne
  have hresult : volume (K : Set Space) ≤ C * familyVolume Fk := by
    apply (ENNReal.mul_le_mul_iff_left htube0 htubeTop).mp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hchain
  have hfamily : Fk = S.fiberFamily k := by
    rfl
  rw [hfamily] at hresult
  exact hresult

/-- The uniform fine-tube volume upper bound converts the fibre body mass to
the exact cardinality of the same Sticky fibre. -/
theorem parentVolume_le_frostman_mul_fiberCardScale
    (S : StickyScaleCover fine rho) (hdelta : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (k : Fin S.coarseCard) (hk : (S.fiber k).Nonempty)
    {C : ENNReal}
    (hF : IsFrostmanOn C fine.bodyFamily (S.fiber k)
      (S.coarse.tubes k).body) :
    volume (S.coarse.tubes k).carrier <=
      C * ((S.fiber k).card : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
  have hbody : familyVolume (S.fiberFamily k) <=
      ((S.fiber k).card : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
    unfold familyVolume StickyScaleCover.fiberFamily
    calc
      (∑ i : {i // i ∈ S.fiber k},
          volume (fine.bodyFamily i.1 : Set Space)) <=
        ∑ _i : {i // i ∈ S.fiber k},
          8 * (delta : ENNReal) ^ 2 := by
            exact Finset.sum_le_sum fun i _ =>
              (fine.tubes i.1).volume_le_eight_mul_sq_of_le_half hdeltaHalf
      _ = ((S.fiber k).card : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_coe]
  calc
    volume (S.coarse.tubes k).carrier <=
        C * familyVolume (S.fiberFamily k) :=
      parentVolume_le_frostman_mul_fiberFamilyVolume
        S hdelta k hk hF
    _ <= C * (((S.fiber k).card : ENNReal) *
        (8 * (delta : ENNReal) ^ 2)) := mul_le_mul' le_rfl hbody
    _ = C * ((S.fiber k).card : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by ring

#print axioms parentVolume_le_frostman_mul_fiberFamilyVolume
#print axioms parentVolume_le_frostman_mul_fiberCardScale

end
end Family8StickyFiberFrostmanParentCardScaleV3
