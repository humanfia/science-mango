import Family8Grounding.Family8FiniteRandomRigidMotionPaperConflictTailV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
import FamilyStickyGrounding.FamilyStickyRandomModelTubeCollisionGridV1
import Submission.Kakeya.ConvexFactoring.FrameBoxVolume
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperGeneralRigidHundredLoadCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
open Family8FiniteRandomRigidMotionPaperConflictTailV1
open Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
open FamilyStickyRandomModelTubeCollisionGridV1

noncomputable section

/-!
# A source-Katz--Tao cap for one general rigid-motion hundred load

For an arbitrary rigid motion, first move the whole source family, then apply
the honest eighth normalization.  Rigid motion preserves the source
Katz--Tao constant, while eighth normalization costs the existing factor
`128`.  Every tube counted by one `normalizedRigidHundredLoadNat` contributes
at least `(delta / 8)^2 / 2` mass inside the test `hundredTube`.  This gives
the exact paper single-load ratio and, using the literal aligned-box volume
of `hundredTube`, the radius-free bound

`load <= 143360000 * C`.

The constant is deliberately only absolute; the useful point is dependence
on the source Katz--Tao constant `C`, rather than on the source cardinality.
This file selects no random tuple and proves no conflict refinement, CWA,
Frostman, or copied-cardinality conclusion.
-/

/-- One rigidly moved copy, still indexed by the original source type. -/
def fixedRigidCopyTubeFamily
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (R : RigidMotion) (F : UniformTubeFamily delta iota) :
    UniformTubeFamily delta iota where
  tubes i := rigidTube R (F.tubes i)
  refinement := F.refinement

@[simp] theorem fixedRigidCopyTubeFamily_tubes
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (R : RigidMotion) (F : UniformTubeFamily delta iota) (i : iota) :
    (fixedRigidCopyTubeFamily R F).tubes i =
      rigidTube R (F.tubes i) :=
  rfl

/-- Transport the source shading along the same fixed rigid motion. -/
def fixedRigidCopyShading
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (R : RigidMotion) (D : ActualTubeDatum delta iota) :
    Shading (fixedRigidCopyTubeFamily R D.family).bodyFamily where
  carrier i := R '' D.shading.carrier i
  measurable_carrier i :=
    R.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (D.shading.measurable_carrier i)
  carrier_subset i := by
    rw [UniformTubeFamily.bodyFamily_apply, Tube.coe_body,
      fixedRigidCopyTubeFamily_tubes, rigidTube_carrier]
    exact Set.image_mono (D.shading.carrier_subset i)

/-- The fixed moved family packaged only so that the existing normalized
Katz--Tao transport theorem can be applied to it. -/
def fixedRigidCopyDatum
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (R : RigidMotion) (D : ActualTubeDatum delta iota) :
    ActualTubeDatum delta iota where
  family := fixedRigidCopyTubeFamily R D.family
  shading := fixedRigidCopyShading R D

@[simp] theorem fixedRigidCopyDatum_family_bodyFamily
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (R : RigidMotion) (D : ActualTubeDatum delta iota) :
    (fixedRigidCopyDatum R D).family.bodyFamily =
      Family8RigidCopyPolynomialJohnKatzTaoV1.fixedRigidCopyBodyFamily
        R D.family :=
  rfl

/-- Rigid transport of the source Katz--Tao certificate, in datum form. -/
theorem fixedRigidCopyDatum_isKatzTao
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {C : ENNReal}
    (R : RigidMotion) (D : ActualTubeDatum delta iota)
    (hKT : IsKatzTao C D.family.bodyFamily) :
    IsKatzTao C (fixedRigidCopyDatum R D).family.bodyFamily := by
  rw [fixedRigidCopyDatum_family_bodyFamily]
  exact fixedRigidCopyBodyFamily_isKatzTao R D.family hKT

/-- On the full admissible normalized range `rho <= 1/16`, the literal
`hundredTube` has volume at most an absolute multiple of `rho^2`.

The enclosing aligned box has full side lengths
`200 rho, 200 rho, 1 + 200 rho`; the last one is at most `14`. -/
theorem volume_hundredTube_le_fiveHundredSixtyThousand_mul_sq
    {rho : NNReal} (W : Tube rho) (hrho : rho <= (1 / 16 : NNReal)) :
    volume (hundredTube W).carrier <=
      (560000 : ENNReal) * (rho : ENNReal) ^ 2 := by
  obtain ⟨frame, hframe⟩ := W.exists_alignedFrame
  have hframeHundred :
      frame 2 = (hundredTube W).axis.direction := by
    simpa only [hundredTube_axis] using hframe
  have hsubset :
      (hundredTube W).carrier ⊆
        ((hundredTube W).alignedFrameBox frame).carrier :=
    (hundredTube W).carrier_subset_alignedFrameBox frame hframeHundred
  have hbox :
      volume ((hundredTube W).alignedFrameBox frame).carrier =
        (40000 : ENNReal) * (rho : ENNReal) ^ 2 *
          (1 + 200 * (rho : ENNReal)) := by
    rw [FrameBox.volume_carrier]
    simp [Tube.alignedFrameBox, Tube.frameBoxSides, hundredRadius,
      Fin.prod_univ_three]
    ring
  have hfactorNN : 1 + 200 * rho <= (14 : NNReal) := by
    nlinarith
  have hfactor :
      (1 : ENNReal) + 200 * (rho : ENNReal) <= 14 := by
    exact_mod_cast hfactorNN
  calc
    volume (hundredTube W).carrier <=
        volume ((hundredTube W).alignedFrameBox frame).carrier :=
      measure_mono hsubset
    _ = (40000 : ENNReal) * (rho : ENNReal) ^ 2 *
        (1 + 200 * (rho : ENNReal)) := hbox
    _ <= (40000 : ENNReal) * (rho : ENNReal) ^ 2 * 14 := by
      exact mul_le_mul_of_nonneg_left hfactor bot_le
    _ = (560000 : ENNReal) * (rho : ENNReal) ^ 2 := by ring

/-- Exact ENNReal mass inequality behind the paper single-load cap. -/
theorem normalizedRigidHundredLoadNat_mul_halfSq_le_sourceKatzTao
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hKT : IsKatzTao C D.family.bodyFamily)
    (testTube : testIndex -> Tube (delta / 8))
    (K : testIndex) (g : motionChoice) :
    (normalizedRigidHundredLoadNat motion D testTube K g : ENNReal) *
        (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) <=
      (128 * C) * volume (hundredTube (testTube K)).carrier := by
  classical
  let moved : ActualTubeDatum delta iota :=
    fixedRigidCopyDatum (motion g) D
  let hits : Finset iota :=
    (Finset.univ : Finset iota).filter fun i =>
      (eighthNormalizedTube
        (rigidTube (motion g) (D.family.tubes i))).carrier ⊆
          (hundredTube (testTube K)).carrier
  have hload :
      normalizedRigidHundredLoadNat motion D testTube K g = hits.card := by
    rfl
  have hsubset :
      hits ⊆ containedIndices
        (eighthNormalizedDatum moved).family.bodyFamily
        (hundredTube (testTube K)).body := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [mem_containedIndices]
    simpa only [moved, fixedRigidCopyDatum,
      fixedRigidCopyTubeFamily_tubes,
      eighthNormalizedDatum_family, eighthNormalizedTubeFamily_tubes,
      UniformTubeFamily.bodyFamily_apply, Tube.coe_body] using hi.2
  have hrhoHalf : delta / 8 <= (2 : NNReal)⁻¹ := by
    exact (div_le_self (show 0 <= delta from bot_le)
      (by norm_num : (1 : NNReal) <= 8)).trans hD.delta_le_half
  have hlower :
      (hits.card : ENNReal) *
          (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) <=
        containedMass
          (eighthNormalizedDatum moved).family.bodyFamily
          (hundredTube (testTube K)).body := by
    calc
      (hits.card : ENNReal) *
          (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) =
          ∑ _i ∈ hits,
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) := by
              simp [nsmul_eq_mul]
      _ <= ∑ i ∈ hits,
          volume ((eighthNormalizedDatum moved).family.tubes i).carrier := by
        apply Finset.sum_le_sum
        intro i _hi
        exact Tube.half_sq_le_volume_of_le_half
          ((eighthNormalizedDatum moved).family.tubes i) hrhoHalf
      _ <= ∑ i ∈ containedIndices
          (eighthNormalizedDatum moved).family.bodyFamily
          (hundredTube (testTube K)).body,
          volume ((eighthNormalizedDatum moved).family.tubes i).carrier := by
        exact Finset.sum_le_sum_of_subset hsubset
      _ = containedMass
          (eighthNormalizedDatum moved).family.bodyFamily
          (hundredTube (testTube K)).body := by rfl
  have hmovedKT :
      IsKatzTao C (fixedRigidCopyDatum (motion g) D).family.bodyFamily :=
    fixedRigidCopyDatum_isKatzTao (motion g) D hKT
  have hnormalizedKT :
      IsKatzTao (128 * C)
        (eighthNormalizedDatum moved).family.bodyFamily := by
    exact eighthNormalizedDatum_isKatzTao moved hD.delta_le_half
      (by simpa only [moved] using hmovedKT)
  calc
    (normalizedRigidHundredLoadNat motion D testTube K g : ENNReal) *
        (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) =
      (hits.card : ENNReal) *
        (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) := by rw [hload]
    _ <= containedMass
        (eighthNormalizedDatum moved).family.bodyFamily
        (hundredTube (testTube K)).body := hlower
    _ <= (128 * C) * volume (hundredTube (testTube K)).carrier :=
      hnormalizedKT (hundredTube (testTube K)).body

/-- The exact real-valued paper cap for one general-rigid-motion test. -/
def normalizedRigidHundredPaperSingleLoadCap
    {delta : NNReal} (C : ENNReal) (W : Tube (delta / 8)) : Real :=
  (((128 * C) * volume (hundredTube W).carrier /
    (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)).toReal)

/-- General-rigid analogue of the translation-only paper single-load cap.
It is uniform in the chosen rigid motion and the test index. -/
theorem normalizedRigidHundredLoadNat_le_paperSingleLoadCap
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (testTube : testIndex -> Tube (delta / 8))
    (K : testIndex) (g : motionChoice) :
    (normalizedRigidHundredLoadNat motion D testTube K g : Real) <=
      normalizedRigidHundredPaperSingleLoadCap C (testTube K) := by
  let floor : ENNReal :=
    ((delta / 8 : NNReal) : ENNReal) ^ 2 / 2
  let total : ENNReal :=
    (128 * C) * volume (hundredTube (testTube K)).carrier
  have hrhoPos : 0 < delta / 8 := div_pos hD.delta_pos (by norm_num)
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
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hCfinite)
      (hundredTube (testTube K)).volume_lt_top.ne
  have hquotientTop : total / floor ≠ ∞ :=
    ENNReal.div_ne_top htotalTop hfloor0
  have hmass :=
    normalizedRigidHundredLoadNat_mul_halfSq_le_sourceKatzTao
      motion D hD hKT testTube K g
  have hquotient :
      (normalizedRigidHundredLoadNat motion D testTube K g : ENNReal) <=
        total / floor := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hfloor0) (Or.inl hfloorTop)).2
    simpa only [total, floor] using hmass
  have hreal := ENNReal.toReal_mono hquotientTop hquotient
  simpa only [normalizedRigidHundredPaperSingleLoadCap,
    total, floor, ENNReal.toReal_natCast] using hreal

/-- Cancellation of the common normalized squared radius in the absolute
hundred-tube volume envelope. -/
theorem normalizedRigidHundredKatzTaoRatio_eq
    {delta : NNReal} (hdeltaPos : 0 < delta)
    {C : ENNReal} (hCfinite : C ≠ ∞) :
    (128 * C) *
          ((560000 : ENNReal) *
            ((delta / 8 : NNReal) : ENNReal) ^ 2) /
        (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) =
      143360000 * C := by
  have hrhoPos : 0 < delta / 8 := div_pos hdeltaPos (by norm_num)
  have hrho0 : (((delta / 8 : NNReal) : ENNReal)) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hrhoPos.ne'
  have hden0 :
      (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨pow_ne_zero 2 hrho0, by norm_num⟩
  have hnumTop :
      (128 * C) *
          ((560000 : ENNReal) *
            ((delta / 8 : NNReal) : ENNReal) ^ 2) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (by norm_num) hCfinite
    · exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hleftTop :
      (128 * C) *
            ((560000 : ENNReal) *
              ((delta / 8 : NNReal) : ENNReal) ^ 2) /
          (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) ≠ ∞ :=
    ENNReal.div_ne_top hnumTop hden0
  have hrightTop : (143360000 : ENNReal) * C ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCfinite
  apply (ENNReal.toReal_eq_toReal_iff' hleftTop hrightTop).mp
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.coe_div]
  field_simp
  ring

/-- The exact paper cap is bounded by a fixed multiple of the source
Katz--Tao constant, uniformly over all normalized hundred tests. -/
theorem normalizedRigidHundredPaperSingleLoadCap_le_sourceKatzTao
    {delta : NNReal} (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (W : Tube (delta / 8)) :
    normalizedRigidHundredPaperSingleLoadCap C W <=
      (143360000 * C : ENNReal).toReal := by
  have hrhoSmall : delta / 8 <= (1 / 16 : NNReal) := by
    rw [← NNReal.coe_le_coe]
    have hreal' : (delta : Real) <= (((2 : NNReal)⁻¹ : NNReal) : Real) :=
      NNReal.coe_le_coe.mpr hdeltaHalf
    have hreal : (delta : Real) <= (1 / 2 : Real) := by
      simpa using hreal'
    push_cast
    linarith
  have hvolume :=
    volume_hundredTube_le_fiveHundredSixtyThousand_mul_sq W hrhoSmall
  have hratio :
      (128 * C) * volume (hundredTube W).carrier /
          (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) <=
        143360000 * C := by
    calc
      (128 * C) * volume (hundredTube W).carrier /
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) <=
          (128 * C) *
              ((560000 : ENNReal) *
                ((delta / 8 : NNReal) : ENNReal) ^ 2) /
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2) := by
        gcongr
      _ = 143360000 * C :=
        normalizedRigidHundredKatzTaoRatio_eq hdeltaPos hCfinite
  have hrightTop : (143360000 : ENNReal) * C ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCfinite
  unfold normalizedRigidHundredPaperSingleLoadCap
  exact ENNReal.toReal_mono hrightTop hratio

/-- Radius-free, cardinality-independent single-load bound in the exact real
form consumed by the finite Chernoff layer. -/
theorem normalizedRigidHundredLoadNat_le_sourceKatzTao
    {motionChoice iota testIndex : Type}
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal}
    (motion : motionChoice -> RigidMotion)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (testTube : testIndex -> Tube (delta / 8))
    (K : testIndex) (g : motionChoice) :
    (normalizedRigidHundredLoadNat motion D testTube K g : Real) <=
      (143360000 * C : ENNReal).toReal := by
  exact (normalizedRigidHundredLoadNat_le_paperSingleLoadCap
    motion D hD hCfinite hKT testTube K g).trans
      (normalizedRigidHundredPaperSingleLoadCap_le_sourceKatzTao
        hD.delta_pos hD.delta_le_half hCfinite (testTube K))

#print axioms fixedRigidCopyDatum_isKatzTao
#print axioms volume_hundredTube_le_fiveHundredSixtyThousand_mul_sq
#print axioms normalizedRigidHundredLoadNat_mul_halfSq_le_sourceKatzTao
#print axioms normalizedRigidHundredLoadNat_le_paperSingleLoadCap
#print axioms normalizedRigidHundredPaperSingleLoadCap_le_sourceKatzTao
#print axioms normalizedRigidHundredLoadNat_le_sourceKatzTao

end
end Family8FiniteRandomRigidMotionPaperGeneralRigidHundredLoadCapV1
