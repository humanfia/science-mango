import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
import FamilyStickyGrounding.FamilyStickyConvexClosedThickeningBoxGrowthV1
import FamilyStickyGrounding.FamilyStickyScaleChainActualStrictLossWithConstantV1
import FamilyStickyGrounding.FamilyStickyScaleChainNormalizedTerminalObstructionV2
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
open FamilyStickyScaleChainActualStrictLossWithConstantV1.StickyScaleCover
open FamilyStickyScaleChainNormalizedTerminalObstructionV2
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Explicit upper bound for the canonical normalized terminal quantity

The automatic terminal body is a frame box with sides
`familyVolume + 1, 1, 1`.  At a one-step terminal radius `rho`, its canonical
test body is the closed `4 rho` thickening.  The existing exact box-growth
lemma and the uniform tube-volume sandwich give the completely explicit
bound proved below.  No normalized-terminal inequality is assumed.
-/

/-- Widened-box volume for a terminal active family of cardinality at most
`n`, using the uniform upper bound `volume tube <= 8 rho^2`. -/
def automaticTerminalBodyVolumeUpper (n : Nat) (rho : NNReal) : ENNReal :=
  (((n : ENNReal) * (8 * (rho : ENNReal) ^ 2) + 1) +
      8 * (rho : ENNReal)) *
    (1 + 8 * (rho : ENNReal)) ^ 2

/-- The final normalized quantity after also using the lower tube-volume
floor `rho^2 / 2`. -/
def automaticNormalizedTerminalUpper (n : Nat) (rho : NNReal) : ENNReal :=
  (n : ENNReal) * automaticTerminalBodyVolumeUpper n rho /
    ((rho : ENNReal) ^ 2 / 2)
/-- A radius-independent numerator valid on `rho <= 1/2`. -/
def automaticTerminalFiniteConstant (n : Nat) : ENNReal :=
  (n : ENNReal) * (((n : ENNReal) * 2 + 5) * 25)

/-- Coarse but transparent `finite constant / rho^2` upper bound. -/
def automaticNormalizedTerminalCoarseUpper
    (n : Nat) (rho : NNReal) : ENNReal :=
  automaticTerminalFiniteConstant n / ((rho : ENNReal) ^ 2 / 2)

/-- Constant left after extracting the two inverse powers of the endpoint
radius. -/
def automaticTerminalAbsorptionConstant (n : Nat) : ENNReal :=
  2 * automaticTerminalFiniteConstant n

/-- One explicit endpoint threshold simultaneously enforces the tube-volume
regime `theta <= 1/2` and absorbs the finite constant using exponent room
strictly beyond two. -/
def automaticOneStepSmallThetaThreshold
    (n : Nat) (exponent : Real) : NNReal :=
  min (2 : NNReal)⁻¹
    (finiteConstantSmallDeltaThreshold
      (automaticTerminalAbsorptionConstant n) (exponent - 2))

theorem automaticOneStepSmallThetaThreshold_pos
    (n : Nat) (exponent : Real) :
    0 < automaticOneStepSmallThetaThreshold n exponent := by
  rw [automaticOneStepSmallThetaThreshold, lt_min_iff]
  exact ⟨by positivity,
    finiteConstantSmallDeltaThreshold_pos
      (automaticTerminalAbsorptionConstant n) (exponent - 2)⟩

/-- On radii at most one half, the widened automatic body has a fixed
polynomial cardinality bound. -/
theorem automaticTerminalBodyVolumeUpper_le_finiteFactor
    (n : Nat) (rho : NNReal) (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    automaticTerminalBodyVolumeUpper n rho <=
      ((n : ENNReal) * 2 + 5) * 25 := by
  have hrho0 :
      (rho : ENNReal) <= (((2 : NNReal)⁻¹ : NNReal) : ENNReal) :=
    ENNReal.coe_le_coe.mpr hrhoHalf
  have hrho : (rho : ENNReal) <= (2 : ENNReal)⁻¹ := by
    simpa only [ENNReal.coe_inv_two] using hrho0
  have htwo : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hsquare : 8 * (rho : ENNReal) ^ 2 <= 2 := by
    calc
      8 * (rho : ENNReal) ^ 2 <= 8 * ((2 : ENNReal)⁻¹) ^ 2 := by
        gcongr
      _ = 2 * ((2 : ENNReal) * (2 : ENNReal)⁻¹) ^ 2 := by ring
      _ = 2 := by rw [htwo]; norm_num
  have hlinear : 8 * (rho : ENNReal) <= 4 := by
    calc
      8 * (rho : ENNReal) <= 8 * (2 : ENNReal)⁻¹ := by gcongr
      _ = 4 * ((2 : ENNReal) * (2 : ENNReal)⁻¹) := by ring
      _ = 4 := by rw [htwo]; norm_num
  have hfirst :
      (((n : ENNReal) * (8 * (rho : ENNReal) ^ 2) + 1) +
          8 * (rho : ENNReal)) <=
        (n : ENNReal) * 2 + 5 := by
    calc
      (((n : ENNReal) * (8 * (rho : ENNReal) ^ 2) + 1) +
          8 * (rho : ENNReal)) <=
        ((n : ENNReal) * 2 + 1) + 4 := by
          exact add_le_add
            (add_le_add (mul_le_mul' le_rfl hsquare) le_rfl) hlinear
      _ = (n : ENNReal) * 2 + 5 := by ring
  have hsecond : (1 + 8 * (rho : ENNReal)) ^ 2 <= 25 := by
    calc
      (1 + 8 * (rho : ENNReal)) ^ 2 <= (1 + 4) ^ 2 := by gcongr
      _ = 25 := by norm_num
  unfold automaticTerminalBodyVolumeUpper
  exact mul_le_mul' hfirst hsecond

/-- The exact explicit upper is bounded by the simpler finite-constant
quotient on radii at most one half. -/
theorem automaticNormalizedTerminalUpper_le_coarseUpper
    (n : Nat) (rho : NNReal) (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    automaticNormalizedTerminalUpper n rho <=
      automaticNormalizedTerminalCoarseUpper n rho := by
  unfold automaticNormalizedTerminalUpper
  unfold automaticNormalizedTerminalCoarseUpper automaticTerminalFiniteConstant
  gcongr
  exact automaticTerminalBodyVolumeUpper_le_finiteFactor n rho hrhoHalf

/-- Extract the exact two inverse endpoint powers from the coarse quotient. -/
theorem automaticNormalizedTerminalCoarseUpper_le_absorption
    (n : Nat) {rho : NNReal} (rho_pos : 0 < rho) :
    automaticNormalizedTerminalCoarseUpper n rho <=
      automaticTerminalAbsorptionConstant n *
        (rho : ENNReal) ^ (-2 : Real) := by
  let x : ENNReal := (rho : ENNReal)
  have hxpos : 0 < x := ENNReal.coe_pos.mpr rho_pos
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hxTop : x ≠ ∞ := ENNReal.coe_ne_top
  have hdenPos : 0 < x ^ 2 / 2 :=
    ENNReal.div_pos (pow_ne_zero 2 hx0) (by norm_num)
  have hdenTop : x ^ 2 / 2 ≠ ∞ := by finiteness
  have htwo : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hpowCancel : x ^ (-2 : Real) * x ^ 2 = 1 := by
    calc
      x ^ (-2 : Real) * x ^ 2 =
          x ^ (-2 : Real) * x ^ (2 : Real) := by
        exact congrArg (fun y => x ^ (-2 : Real) * y)
          (ENNReal.rpow_natCast x 2).symm
      _ = x ^ ((-2 : Real) + 2) :=
        (ENNReal.rpow_add (-2 : Real) 2 hx0 hxTop).symm
      _ = 1 := by norm_num
  unfold automaticNormalizedTerminalCoarseUpper
  apply (ENNReal.div_le_iff (ne_of_gt hdenPos) hdenTop).2
  change automaticTerminalFiniteConstant n <=
    (automaticTerminalAbsorptionConstant n * x ^ (-2 : Real)) *
      (x ^ 2 / 2)
  apply le_of_eq
  symm
  unfold automaticTerminalAbsorptionConstant
  rw [ENNReal.div_eq_inv_mul]
  calc
    (2 * automaticTerminalFiniteConstant n * x ^ (-2 : Real)) *
        ((2 : ENNReal)⁻¹ * x ^ 2) =
      automaticTerminalFiniteConstant n *
        ((2 : ENNReal) * (2 : ENNReal)⁻¹) *
        (x ^ (-2 : Real) * x ^ 2) := by ring
    _ = automaticTerminalFiniteConstant n := by
      rw [htwo, hpowCancel]
      simp

/-- Exponent room strictly beyond two and the explicit small-theta threshold
automatically absorb the finite cardinality constant. -/
theorem automaticNormalizedTerminalCoarseUpper_le_rpow_of_smallTheta
    (n : Nat) {rho : NNReal} {exponent : Real}
    (rho_pos : 0 < rho) (two_lt_exponent : 2 < exponent)
    (rho_le : rho <= automaticOneStepSmallThetaThreshold n exponent) :
    automaticNormalizedTerminalCoarseUpper n rho <=
      (rho : ENNReal) ^ (-exponent) := by
  have hgap : 0 < exponent - 2 := by linarith
  have hthreshold : rho <=
      finiteConstantSmallDeltaThreshold
        (automaticTerminalAbsorptionConstant n) (exponent - 2) :=
    rho_le.trans (min_le_right _ _)
  have hconstantTop : automaticTerminalAbsorptionConstant n ≠ ∞ := by
    unfold automaticTerminalAbsorptionConstant automaticTerminalFiniteConstant
    finiteness
  have hconstant := finiteConstant_le_delta_negativePower
    hconstantTop hgap rho_pos hthreshold
  have hx0 : (rho : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr rho_pos.ne'
  have hxTop : (rho : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    automaticNormalizedTerminalCoarseUpper n rho <=
        automaticTerminalAbsorptionConstant n *
          (rho : ENNReal) ^ (-2 : Real) :=
      automaticNormalizedTerminalCoarseUpper_le_absorption n rho_pos
    _ <= (rho : ENNReal) ^ (-(exponent - 2)) *
          (rho : ENNReal) ^ (-2 : Real) :=
      mul_le_mul' hconstant le_rfl
    _ = (rho : ENNReal) ^ (-(exponent - 2) + (-2 : Real)) := by
      exact (ENNReal.rpow_add _ _ hx0 hxTop).symm
    _ = (rho : ENNReal) ^ (-exponent) := by
      congr 1
      ring


namespace MultiscaleTubeHierarchy

variable {nominalRadius : Nat -> NNReal} {card : Nat -> Nat}
  (H : MultiscaleTubeHierarchy 1 nominalRadius (fun l => Fin (card l)))

/-- Summing the uniform upper tube-volume bound over the literal terminal
active subtype bounds its total indexed family volume. -/
theorem terminal_familyVolume_le_card_mul_eight_sq
    (hradius : H.effectiveRadius 1 <= (2 : NNReal)⁻¹) :
    familyVolume (effectiveActiveFamily H 1) <=
      (Fintype.card {i // i ∈
          (H.effectiveFamily 1).refinement.refined} : ENNReal) *
        (8 * (H.effectiveRadius 1 : ENNReal) ^ 2) := by
  unfold familyVolume effectiveActiveFamily UniformTubeFamily.bodyFamily
  simp only [Tube.coe_body]
  calc
    (∑ i : {i // i ∈ (H.effectiveFamily 1).refinement.refined},
        volume ((H.effectiveFamily 1).tubes i.1).carrier) <=
      ∑ _i : {i // i ∈ (H.effectiveFamily 1).refinement.refined},
        8 * (H.effectiveRadius 1 : ENNReal) ^ 2 := by
          exact Finset.sum_le_sum fun i _ =>
            ((H.effectiveFamily 1).tubes i.1).volume_le_eight_mul_sq_of_le_half
              hradius
    _ = (Fintype.card {i // i ∈
          (H.effectiveFamily 1).refinement.refined} : ENNReal) *
        (8 * (H.effectiveRadius 1 : ENNReal) ^ 2) := by simp

/-- The attained minimum of the terminal active tube volumes retains the
uniform lower `rho^2 / 2` floor. -/
theorem half_sq_le_terminal_canonicalTubeVolume
    (hradius : H.effectiveRadius 1 <= (2 : NNReal)⁻¹) :
    (H.effectiveRadius 1 : ENNReal) ^ 2 / 2 <=
      canonicalTubeVolume H (by omega) 1 := by
  rw [canonicalTubeVolume_of_le H (by omega) 1 (by omega)]
  rw [activeTubeVolumeFloorAt, Finset.le_inf'_iff]
  intro i _hi
  exact ((H.effectiveFamily 1).tubes i.1).half_sq_le_volume_of_le_half
    hradius

/-- Exact widened-frame-box upper bound for the automatic one-step terminal
test body, before replacing the family volume by a cardinality bound. -/
theorem volume_automaticTerminalTestBody_le_familyVolume_box
    (_hradius : H.effectiveRadius 1 <= (2 : NNReal)⁻¹) :
    volume
        (canonicalTestBody H (canonicalTerminalUnitBody H) 1 : Set Space) <=
      ((familyVolume (effectiveActiveFamily H 1) + 1) +
          8 * (H.effectiveRadius 1 : ENNReal)) *
        (1 + 8 * (H.effectiveRadius 1 : ENNReal)) ^ 2 := by
  rw [canonicalTestBody_succ, canonicalTestBody_zero]
  change volume
      (Metric.cthickening
        ((4 * H.effectiveRadius 1 : NNReal) : Real)
        (canonicalTerminalUnitBody H : Set Space)) <= _
  have hbox :=
    FamilyStickyConvexClosedThickeningBoxGrowthV1.FrameBox.volume_cthickening_le_prod_side_add_two_mul
      (terminalUnitFrameBox (effectiveActiveFamily H 1))
      (canonicalTerminalUnitBody H : Set Space)
      (canonicalTerminalUnitBody H).isCompact
      (by
        intro x hx
        simpa [canonicalTerminalUnitBody, terminalUnitBody] using hx)
      (4 * H.effectiveRadius 1)
  calc
    volume
        (Metric.cthickening
          ((4 * H.effectiveRadius 1 : NNReal) : Real)
          (canonicalTerminalUnitBody H : Set Space)) <=
      ∏ i : Fin 3, (
        ((terminalUnitFrameBox
            (effectiveActiveFamily H 1)).side i : ENNReal) +
          2 * ((4 * H.effectiveRadius 1 : NNReal) : ENNReal)) := hbox
    _ = ((familyVolume (effectiveActiveFamily H 1) + 1) +
          8 * (H.effectiveRadius 1 : ENNReal)) *
        (1 + 8 * (H.effectiveRadius 1 : ENNReal)) ^ 2 := by
      have hside :
          (terminalUnitSide (effectiveActiveFamily H 1) : ENNReal) =
            familyVolume (effectiveActiveFamily H 1) + 1 := by
        rw [terminalUnitSide, ENNReal.coe_add, ENNReal.coe_one,
          ENNReal.coe_toNNReal
            (familyVolume_ne_top (effectiveActiveFamily H 1))]
      rw [Fin.prod_univ_three]
      simp only [terminalUnitFrameBox, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two]
      simp [Matrix.vecHead, Matrix.vecTail, hside]
      ring
/-- Replacing total terminal family volume by its literal active cardinality
gives a fully finite upper bound for the automatic terminal test body. -/
theorem volume_automaticTerminalTestBody_le_activeCardUpper
    (hradius : H.effectiveRadius 1 <= (2 : NNReal)⁻¹) :
    volume
        (canonicalTestBody H (canonicalTerminalUnitBody H) 1 : Set Space) <=
      automaticTerminalBodyVolumeUpper
        (Fintype.card {i // i ∈
          (H.effectiveFamily 1).refinement.refined})
        (H.effectiveRadius 1) := by
  refine (volume_automaticTerminalTestBody_le_familyVolume_box H hradius).trans ?_
  unfold automaticTerminalBodyVolumeUpper
  gcongr
  exact terminal_familyVolume_le_card_mul_eight_sq H hradius

end MultiscaleTubeHierarchy

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (C : CoherentStickyMultiscaleCover fine)
  {outerDepth : Nat}

/-- The active fine cardinality of a coherent interval is bounded by the
original fine index cardinality. -/
theorem interval_activeFine_card_le_original_card
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (m : Fin outerDepth) :
    ((F.chain m).intervalCover C 0 (by omega)).activeFine.card <=
      Fintype.card iota := by
  let I := (F.chain m).intervalCover C 0 (by omega)
  let B := (F.chain m).selectedCover C 0
  change I.activeFine.card <= Fintype.card iota
  calc
    I.activeFine.card = B.activeCoarse.card := by rfl
    _ <= B.activeFine.card := activeCoarse_card_le_activeFine_card B
    _ <= Fintype.card iota := Finset.card_le_univ B.activeFine

/-- The terminal active subtype is also bounded by the original fine index
cardinality, despite arbitrary inactive indices in the supplied coarse type. -/
theorem terminal_activeCard_le_original_card
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (m : Fin outerDepth) :
    Fintype.card {i // i ∈
        ((F.hierarchy m).effectiveFamily 1).refinement.refined} <=
      Fintype.card iota := by
  let B := (F.chain m).selectedCover C 1
  change Fintype.card {i // i ∈ B.coarse.refinement.refined} <=
    Fintype.card iota
  rw [<- B.activeCoarse_eq_refined, Fintype.card_coe]
  exact (activeCoarse_card_le_activeFine_card B).trans
    (Finset.card_le_univ B.activeFine)

/-- Main explicit result.  For the automatic terminal body, the exact
canonical normalized terminal quantity is bounded solely by the original
fine-family cardinality and the hierarchy's terminal effective radius. -/
theorem automatic_normalizedTerminal_le_originalCardUpper
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (delta_pos : 0 < delta)
    (m : Fin outerDepth)
    (hradius : (F.hierarchy m).effectiveRadius 1 <= (2 : NNReal)⁻¹) :
    canonicalOneStepNormalizedTerminalAt C F
        (fun k => canonicalTerminalUnitBody (F.hierarchy k)) m <=
      automaticNormalizedTerminalUpper (Fintype.card iota)
        ((F.hierarchy m).effectiveRadius 1) := by
  let H := F.hierarchy m
  have hvol :=
    MultiscaleTubeHierarchy.volume_automaticTerminalTestBody_le_activeCardUpper
      H hradius
  have hcardTerminal :
      (Fintype.card {i // i ∈
        (H.effectiveFamily 1).refinement.refined} : ENNReal) <=
        (Fintype.card iota : ENNReal) := by
    exact_mod_cast terminal_activeCard_le_original_card C F m
  have hbody :
      volume (canonicalTestBody H (canonicalTerminalUnitBody H) 1 : Set Space) <=
        automaticTerminalBodyVolumeUpper (Fintype.card iota)
          (H.effectiveRadius 1) := by
    exact hvol.trans (by
      unfold automaticTerminalBodyVolumeUpper
      gcongr)
  have hfloor :=
    MultiscaleTubeHierarchy.half_sq_le_terminal_canonicalTubeVolume H hradius
  have hinitialCard :
      (((F.chain m).intervalCover C 0 (by omega)).activeFine.card : ENNReal) <=
        (Fintype.card iota : ENNReal) := by
    exact_mod_cast interval_activeFine_card_le_original_card C F m
  unfold canonicalOneStepNormalizedTerminalAt automaticNormalizedTerminalUpper
  rw [← mul_div_assoc]
  apply ENNReal.div_le_of_le_mul
  calc
    (((F.chain m).intervalCover C 0 (by omega)).activeFine.card : ENNReal) *
        volume
          (canonicalTestBody (F.hierarchy m)
            (canonicalTerminalUnitBody (F.hierarchy m)) 1 : Set Space) <=
      (Fintype.card iota : ENNReal) *
        automaticTerminalBodyVolumeUpper (Fintype.card iota)
          ((F.hierarchy m).effectiveRadius 1) := mul_le_mul' hinitialCard hbody
    _ = automaticNormalizedTerminalUpper (Fintype.card iota)
          ((F.hierarchy m).effectiveRadius 1) *
        (((F.hierarchy m).effectiveRadius 1 : ENNReal) ^ 2 / 2) := by
      unfold automaticNormalizedTerminalUpper
      have hrho :
          0 < ((F.hierarchy m).effectiveRadius 1 : ENNReal) :=
        ENNReal.coe_pos.mpr
          (coherentHierarchy_effectiveRadius_pos F delta_pos m 1)
      have hpos :
          0 < ((F.hierarchy m).effectiveRadius 1 : ENNReal) ^ 2 / 2 := by
        exact ENNReal.div_pos (ENNReal.pow_pos hrho 2).ne' (by norm_num)
      have htop :
          ((F.hierarchy m).effectiveRadius 1 : ENNReal) ^ 2 / 2 ≠ ∞ := by
        finiteness
      rw [ENNReal.div_mul_cancel hpos.ne' htop]
    _ <= automaticNormalizedTerminalUpper (Fintype.card iota)

          ((F.hierarchy m).effectiveRadius 1) *
        canonicalTubeVolume (F.hierarchy m) (by omega) 1 := by
      gcongr

/-! ## Direct endpoint producer for a canonical scale sequence -/

/-- For the literal canonical interval `tau_m -> theta_m`, the automatic
normalized terminal quantity is bounded by the finite constant over
`theta_m^2`. -/
theorem ofFiniteScaleSequence_automatic_normalizedTerminal_le_coarseUpper
    (S : FiniteScaleSequence delta outerDepth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta) (m : Fin outerDepth)
    (theta_le_half : S.theta m <= (2 : NNReal)⁻¹) :
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
      C S fine_refined_nonempty
    canonicalOneStepNormalizedTerminalAt C F
        (fun k => canonicalTerminalUnitBody (F.hierarchy k)) m <=
      automaticNormalizedTerminalCoarseUpper (Fintype.card iota)
        (S.theta m) := by
  dsimp only
  let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
    C S fine_refined_nonempty
  have heffective : (F.hierarchy m).effectiveRadius 1 = S.theta m :=
    CoherentExactHierarchyFamily.ofFiniteScaleSequence_effectiveRadius_one
      C S fine_refined_nonempty m
  have heffective_half :
      (F.hierarchy m).effectiveRadius 1 <= (2 : NNReal)⁻¹ := by
    simpa only [heffective] using theta_le_half
  calc
    canonicalOneStepNormalizedTerminalAt C F
          (fun k => canonicalTerminalUnitBody (F.hierarchy k)) m <=
        automaticNormalizedTerminalUpper (Fintype.card iota)
          ((F.hierarchy m).effectiveRadius 1) :=
      automatic_normalizedTerminal_le_originalCardUpper C F delta_pos m
        heffective_half
    _ <= automaticNormalizedTerminalCoarseUpper (Fintype.card iota)
          ((F.hierarchy m).effectiveRadius 1) :=
      automaticNormalizedTerminalUpper_le_coarseUpper
        (Fintype.card iota) ((F.hierarchy m).effectiveRadius 1)
          heffective_half
    _ = automaticNormalizedTerminalCoarseUpper (Fintype.card iota)
          (S.theta m) := by rw [heffective]

/-- A genuinely explicit numerical threshold now directly constructs the
analytic atom consumed by the canonical one-step envelope theorem.  The
premise mentions only the displayed finite constant, the endpoint radius,
and the requested exponent; it does not repeat the normalized target. -/
def ofFiniteScaleSequence_automatic_oneStepExponentBound
    (S : FiniteScaleSequence delta outerDepth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (profile : Nat -> Real) (stage : Nat) (m : Fin outerDepth)
    (theta_le_half : S.theta m <= (2 : NNReal)⁻¹)
    (finiteConstant_threshold :
      automaticNormalizedTerminalCoarseUpper (Fintype.card iota)
          (S.theta m) <=
        (S.theta m : ENNReal) ^ (-profile (stage - 1))) :
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
      C S fine_refined_nonempty
    OneStepNormalizedTerminalExponentBound C F
      (fun k => canonicalTerminalUnitBody (F.hierarchy k))
      S profile stage m := by
  dsimp only
  refine {
    exponent := -profile (stage - 1)
    normalizedTerminal_upper := ?_
    exponent_balance := le_rfl }
  exact
    (ofFiniteScaleSequence_automatic_normalizedTerminal_le_coarseUpper
      C S fine_refined_nonempty delta_pos m theta_le_half).trans
      finiteConstant_threshold

/-- Fully automatic version: a profile exponent strictly larger than two and
the single explicit small-theta condition produce the analytic package. -/
def ofFiniteScaleSequence_automatic_oneStepExponentBound_of_smallTheta
    (S : FiniteScaleSequence delta outerDepth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (profile : Nat -> Real) (stage : Nat) (m : Fin outerDepth)
    (profile_gt_two : 2 < profile (stage - 1))
    (theta_le_threshold : S.theta m <=
      automaticOneStepSmallThetaThreshold (Fintype.card iota)
        (profile (stage - 1))) :
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
      C S fine_refined_nonempty
    OneStepNormalizedTerminalExponentBound C F
      (fun k => canonicalTerminalUnitBody (F.hierarchy k))
      S profile stage m := by
  have theta_pos : 0 < S.theta m :=
    delta_pos.trans_le ((S.delta_le_tau m).trans (S.tau_le_theta m))
  have theta_le_half : S.theta m <= (2 : NNReal)⁻¹ :=
    theta_le_threshold.trans (min_le_left _ _)
  apply ofFiniteScaleSequence_automatic_oneStepExponentBound
    C S fine_refined_nonempty delta_pos profile stage m theta_le_half
  exact automaticNormalizedTerminalCoarseUpper_le_rpow_of_smallTheta
    (Fintype.card iota) theta_pos profile_gt_two theta_le_threshold


/-! ## Sharp endpoint limitation -/

/-- At an endpoint `theta = 1`, the required power is exactly one for every
profile.  Hence an automatic-body exponent package is impossible as soon as
the proved active-cardinality lower bound is strictly larger than one.  This
formally rules out absorbing all intervals merely by taking `delta` small. -/
theorem not_nonempty_automatic_oneStepExponentBound_of_theta_eq_one
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (delta_pos : 0 < delta)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat) (m : Fin outerDepth)
    (theta_eq_one : S.theta m = 1)
    (one_lt_cardProduct :
      1 <
        (((F.chain m).intervalCover C 0 (by omega)).activeFine.card : ENNReal) *
          (canonicalTerminalActiveCardAt C F m : ENNReal)) :
    ¬ Nonempty (OneStepNormalizedTerminalExponentBound C F
      (automaticTerminalInitialBody C F) S profile stage m) := by
  rintro ⟨bound⟩
  have hcard := activeCardProduct_le_requiredPower_of_automaticBound
    C F delta_pos S profile stage m bound
  rw [theta_eq_one] at hcard
  simp only [ENNReal.coe_one, ENNReal.one_rpow] at hcard
  exact (not_le_of_gt one_lt_cardProduct) hcard

#print axioms MultiscaleTubeHierarchy.terminal_familyVolume_le_card_mul_eight_sq
#print axioms MultiscaleTubeHierarchy.half_sq_le_terminal_canonicalTubeVolume
#print axioms MultiscaleTubeHierarchy.volume_automaticTerminalTestBody_le_familyVolume_box
#print axioms MultiscaleTubeHierarchy.volume_automaticTerminalTestBody_le_activeCardUpper
#print axioms interval_activeFine_card_le_original_card
#print axioms terminal_activeCard_le_original_card
#print axioms automatic_normalizedTerminal_le_originalCardUpper
#print axioms automaticTerminalBodyVolumeUpper_le_finiteFactor
#print axioms automaticNormalizedTerminalUpper_le_coarseUpper
#print axioms automaticOneStepSmallThetaThreshold_pos
#print axioms automaticNormalizedTerminalCoarseUpper_le_absorption
#print axioms automaticNormalizedTerminalCoarseUpper_le_rpow_of_smallTheta
#print axioms ofFiniteScaleSequence_automatic_normalizedTerminal_le_coarseUpper
#print axioms ofFiniteScaleSequence_automatic_oneStepExponentBound
#print axioms ofFiniteScaleSequence_automatic_oneStepExponentBound_of_smallTheta
#print axioms not_nonempty_automatic_oneStepExponentBound_of_theta_eq_one

end
end FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
