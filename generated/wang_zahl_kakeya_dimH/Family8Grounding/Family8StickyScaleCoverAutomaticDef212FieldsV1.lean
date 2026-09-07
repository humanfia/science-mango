import Family8Grounding.Family8FiniteFibreAutomaticCWAV3
import Family8Grounding.Family8TubeJohnUnitRescalingGeometryLeOneV7

/-!
# Automatic finite Definition 2.12 fields for one sticky scale cover

For a finite sticky cover at positive radius at most one, John normalization
and rescaled-fibre CWA exist with a finite data-dependent natural constant.
Finite occupied fibres are also automatically C-uniform with a cardinality
constant.  This does not produce doubled-parent partitioning and makes no
claim that the resulting constant is uniform as the fine scale tends to zero.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyScaleCoverAutomaticDef212FieldsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8FiniteFibreAutomaticCWAV3
open Family8TubeJohnUnitRescalingGeometryLeOneV7
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- Convex Wolff control is monotone in its constant. -/
theorem satisfiesConvexWolffAxioms_mono
    {index : Type} [Fintype index]
    {C C' : ENNReal} {F : ConvexFamily index}
    (h : SatisfiesConvexWolffAxioms C F) (hCC' : C <= C') :
    SatisfiesConvexWolffAxioms C' F := by
  intro K
  exact (h K).trans
    (mul_le_mul' (mul_le_mul' hCC' le_rfl) le_rfl)

/-- The fibrewise version is monotone in the same constant. -/
theorem fibresSatisfyCWA_mono
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {S : StickyScaleCover fine rho}
    {R : UnitRescalingGeometry S} {C C' : ENNReal}
    (h : R.FibresSatisfyCWA C) (hCC' : C <= C') :
    R.FibresSatisfyCWA C' := by
  intro k
  exact satisfiesConvexWolffAxioms_mono (h k) hCC'


/-- C-uniformity is monotone in its constant. -/
theorem isCUniform_mono
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {S : StickyScaleCover fine rho} {C C' : ENNReal}
    (h : IsCUniform S C) (hCC' : C <= C') :
    IsCUniform S C' := by
  intro k hk l hl
  exact (h k hk l hl).trans
    (mul_le_mul' hCC' le_rfl)

/-- Every member of every rescaled fibre of an arbitrary sticky cover has
positive volume, because it is an invertible affine image of a fine tube. -/
theorem StickyScaleCover.rescaledFiberFamily_volume_pos
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) (hdeltaPos : 0 < delta)
    (R : UnitRescalingGeometry S) :
    forall k i,
      0 < volume (R.rescaledFiberFamily k i : Set Space) := by
  intro k i
  change 0 < volume
    (affineImageConvexBody (R.unitRescaling k)
      (S.fiberFamily k.1 i) : Set Space)
  rw [volume_affineImageConvexBody]
  have hfiberVolume : 0 < volume (S.fiberFamily k.1 i : Set Space) := by
    simpa only [StickyScaleCover.fiberFamily,
      UniformTubeFamily.bodyFamily_apply, Tube.coe_body] using
      (fine.tubes i.1).volume_pos hdeltaPos
  exact ENNReal.mul_pos (affineJacobian_pos (R.unitRescaling k)).ne'
    hfiberVolume.ne'

/-- A universal finite cardinality constant for one fine index type. -/
def automaticCUniformNat (iota : Type) [Fintype iota] : Nat :=
  max 1 (Fintype.card iota)

theorem one_le_automaticCUniformNat
    (iota : Type) [Fintype iota] :
    1 <= automaticCUniformNat iota :=
  Nat.le_max_left _ _

/-- Every finite sticky cover is C-uniform with the cardinality constant.
The proof uses only that each active parent has a nonempty assigned fibre. -/
theorem StickyScaleCover.isCUniform_automatic
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) :
    IsCUniform S (automaticCUniformNat iota : ENNReal) := by
  intro k hk l hl
  have hlone : 1 <= (S.fiber l).card := by
    apply Finset.one_le_card.mpr
    obtain ⟨i, hi, hparent⟩ := S.parent_surjective l hl
    exact ⟨i, (S.mem_fiber i l).mpr ⟨hi, hparent⟩⟩
  have hnat : (S.fiber k).card <=
      automaticCUniformNat iota * (S.fiber l).card := by
    calc
      (S.fiber k).card <= Fintype.card iota := Finset.card_le_univ _
      _ <= automaticCUniformNat iota := Nat.le_max_right _ _
      _ = automaticCUniformNat iota * 1 := (Nat.mul_one _).symm
      _ <= automaticCUniformNat iota * (S.fiber l).card :=
        Nat.mul_le_mul_left _ hlone
  exact_mod_cast hnat

/-- One arbitrary positive-radius cover at radius at most one carries all
non-partition Definition 2.12 fields with one finite natural constant. -/
theorem StickyScaleCover.exists_nat_tubeJohn_cUniform_fibresCWA_of_le_one
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho)
    (hdeltaPos : 0 < delta) (hrhoPos : 0 < rho) (hrhoOne : rho <= 1) :
    exists Cnn : Nat, 1 <= Cnn ∧
      IsCUniform S (Cnn : ENNReal) ∧
      let R :=
        Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnUnitRescalingGeometry_of_le_one
          S hrhoPos hrhoOne
      R.FibresSatisfyCWA (Cnn : ENNReal) := by
  let R := Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnUnitRescalingGeometry_of_le_one
    S hrhoPos hrhoOne
  obtain ⟨Ccwa, hCcwa, hCWA⟩ :=
    exists_nat_fibresSatisfyCWA_of_volume_pos R
      (Family8StickyScaleCoverAutomaticDef212FieldsV1.StickyScaleCover.rescaledFiberFamily_volume_pos
        S hdeltaPos R)
  let Cnn := max (automaticCUniformNat iota) Ccwa
  refine ⟨Cnn, ?_, ?_, ?_⟩
  · exact (one_le_automaticCUniformNat iota).trans
      (Nat.le_max_left _ _)
  · exact isCUniform_mono
      (Family8StickyScaleCoverAutomaticDef212FieldsV1.StickyScaleCover.isCUniform_automatic
        S) (by
        exact_mod_cast (Nat.le_max_left
          (automaticCUniformNat iota) Ccwa))
  · exact fibresSatisfyCWA_mono hCWA (by
      exact_mod_cast (Nat.le_max_right
        (automaticCUniformNat iota) Ccwa))

#print axioms satisfiesConvexWolffAxioms_mono
#print axioms fibresSatisfyCWA_mono
#print axioms StickyScaleCover.rescaledFiberFamily_volume_pos
#print axioms StickyScaleCover.isCUniform_automatic
#print axioms
  StickyScaleCover.exists_nat_tubeJohn_cUniform_fibresCWA_of_le_one

end
end Family8StickyScaleCoverAutomaticDef212FieldsV1
