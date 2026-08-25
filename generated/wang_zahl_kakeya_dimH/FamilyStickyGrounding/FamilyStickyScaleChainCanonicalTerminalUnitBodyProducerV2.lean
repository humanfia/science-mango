import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2
import Submission.Kakeya.ConvexFactoring.FrameBoxVolume
import Submission.Kakeya.ConvexFactoring.NonConcentration

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyAdjacentTestBodyGeometryV1
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2.MultiscaleTubeHierarchy

noncomputable section

/-!
# Automatic terminal unit body for canonical buffered chains

For a finite convex family, its total indexed volume is finite.  We build an
explicit frame box of side lengths `(familyVolume + 1) x 1 x 1`; its volume
dominates the whole family volume and is strictly positive.  Any later
canonical thickening contains this initial box, so the terminal concentration
is at most one.  This removes the external `top_le_one` premise from the
canonical `BufferedTestBodyChain` producer without replacing it by an
equivalent assumption.
-/

/-! ## A volume-dominating explicit convex body -/

/-- A concrete ambient orthonormal frame. -/
def terminalStandardFrame : OrthonormalBasis (Fin 3) Real Space :=
  (stdOrthonormalBasis Real Space).reindex (finCongr (by simp [Space]))

/-- The long side is one more than the finite total indexed family volume. -/
def terminalUnitSide {index : Type*} [Fintype index]
    (F : ConvexFamily index) : NNReal :=
  (familyVolume F).toNNReal + 1

/-- Explicit volume-dominating frame box. -/
def terminalUnitFrameBox {index : Type*} [Fintype index]
    (F : ConvexFamily index) : FrameBox where
  center := 0
  frame := terminalStandardFrame
  side := ![terminalUnitSide F, 1, 1]

/-- The corresponding compact nonempty convex body. -/
def terminalUnitBody {index : Type*} [Fintype index]
    (F : ConvexFamily index) : ConvexBody Space :=
  (terminalUnitFrameBox F).body

/-- Exact volume of the explicit body. -/
theorem volume_terminalUnitBody {index : Type*} [Fintype index]
    (F : ConvexFamily index) :
    volume (terminalUnitBody F : Set Space) =
      (terminalUnitSide F : ENNReal) := by
  rw [terminalUnitBody, FrameBox.volume_body]
  simp [terminalUnitFrameBox, Fin.prod_univ_three]

/-- The explicit body has positive volume, even for an empty or zero-volume
family. -/
theorem volume_terminalUnitBody_pos {index : Type*} [Fintype index]
    (F : ConvexFamily index) :
    0 < volume (terminalUnitBody F : Set Space) := by
  rw [volume_terminalUnitBody]
  exact ENNReal.coe_pos.mpr (by simp [terminalUnitSide])

/-- Its volume dominates the total indexed family volume. -/
theorem familyVolume_le_volume_terminalUnitBody
    {index : Type*} [Fintype index] (F : ConvexFamily index) :
    familyVolume F <= volume (terminalUnitBody F : Set Space) := by
  rw [volume_terminalUnitBody]
  calc
    familyVolume F = ((familyVolume F).toNNReal : ENNReal) :=
      (ENNReal.coe_toNNReal (familyVolume_ne_top F)).symm
    _ <= (terminalUnitSide F : ENNReal) := by
      exact_mod_cast (show (familyVolume F).toNNReal <= terminalUnitSide F by
        simp [terminalUnitSide])

/-! ## General concentration closure -/

/-- Any convex body whose volume dominates the whole finite family has
concentration at most one. -/
theorem concentration_le_one_of_familyVolume_le_volume
    {index : Type*} [Fintype index] (F : ConvexFamily index)
    (K : ConvexBody Space)
    (hvolume : familyVolume F <= volume (K : Set Space)) :
    concentration F K <= 1 := by
  rw [concentration_eq_containedMass_div]
  apply ENNReal.div_le_of_le_mul
  simpa using (containedMass_le_familyVolume F K).trans hvolume

/-! ## Canonical hierarchy terminal body -/

namespace MultiscaleTubeHierarchy

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {card : Nat -> Nat}
  (H : MultiscaleTubeHierarchy depth nominalRadius
    (fun l => Fin (card l)))

/-- Apply the explicit volume-dominating body to the terminal active effective
family of a hierarchy. -/
def canonicalTerminalUnitBody : ConvexBody Space :=
  terminalUnitBody (effectiveActiveFamily H depth)

/-- The canonical terminal unit body always has positive ambient volume. -/
theorem canonicalTerminalUnitBody_volume_pos :
    0 < volume (canonicalTerminalUnitBody H : Set Space) := by
  exact volume_terminalUnitBody_pos (effectiveActiveFamily H depth)

/-- Its volume dominates the total volume of every terminal active effective
tube, with repetitions retained by the finite index type. -/
theorem terminal_familyVolume_le_canonicalTerminalUnitBody :
    familyVolume (effectiveActiveFamily H depth) <=
      volume (canonicalTerminalUnitBody H : Set Space) := by
  exact familyVolume_le_volume_terminalUnitBody
    (effectiveActiveFamily H depth)

/-- Every canonical thickening contains its initial body, so the terminal
test body retains the volume domination needed for concentration at most one.
This is the former external `top_le_one` field, now proved from the explicit
body. -/
theorem canonicalTerminalUnitBody_top_le_one :
    concentration (effectiveActiveFamily H depth)
        (canonicalTestBody H (canonicalTerminalUnitBody H) depth) <= 1 := by
  apply concentration_le_one_of_familyVolume_le_volume
  exact (terminal_familyVolume_le_canonicalTerminalUnitBody H).trans
    (measure_mono
      (initial_subset_canonicalTestBody H (canonicalTerminalUnitBody H) depth))

/-- Depth one is the literal terminal body used by adjacent-scale canonical
chains: one closed thickening by `4 * effectiveRadius 1`. -/
theorem canonicalOneStepTerminalUnitBody_top_le_one
    {nominalRadius : Nat -> NNReal} {card : Nat -> Nat}
    (H : MultiscaleTubeHierarchy 1 nominalRadius
      (fun l => Fin (card l))) :
    concentration (effectiveActiveFamily H 1)
      (closedThickeningBody (canonicalTerminalUnitBody H)
        (4 * H.effectiveRadius 1)) <= 1 := by
  simpa using canonicalTerminalUnitBody_top_le_one H


/-! ## Complete canonical chain producer -/

/-- The complete canonical buffered test-body chain with automatic terminal
normalization.  No terminal concentration premise remains. -/
def canonicalBufferedTestBodyChainWithAutomaticTerminal
    (hdepth : 0 < depth)
    (effectiveRadius_pos : forall l, l <= depth ->
      0 < H.effectiveRadius l) :
    BufferedTestBodyChain H :=
  canonicalBufferedTestBodyChain H hdepth effectiveRadius_pos
    (canonicalTerminalUnitBody H)
    (canonicalTerminalUnitBody_volume_pos H)
    (canonicalTerminalUnitBody_top_le_one H)

/-- Convenience producer using positive nominal radii; accumulated buffers
automatically preserve positivity of the effective radii. -/
def canonicalBufferedTestBodyChainOfNominalRadiusPosWithAutomaticTerminal
    (hdepth : 0 < depth)
    (nominalRadius_pos : forall l, l <= depth ->
      0 < nominalRadius l) :
    BufferedTestBodyChain H :=
  canonicalBufferedTestBodyChainWithAutomaticTerminal H hdepth
    (effectiveRadius_pos_of_nominalRadius_pos H nominalRadius_pos)

end MultiscaleTubeHierarchy


#print axioms volume_terminalUnitBody
#print axioms familyVolume_le_volume_terminalUnitBody
#print axioms concentration_le_one_of_familyVolume_le_volume
#print axioms MultiscaleTubeHierarchy.canonicalTerminalUnitBody_volume_pos
#print axioms MultiscaleTubeHierarchy.canonicalTerminalUnitBody_top_le_one
#print axioms MultiscaleTubeHierarchy.canonicalOneStepTerminalUnitBody_top_le_one
#print axioms MultiscaleTubeHierarchy.canonicalBufferedTestBodyChainWithAutomaticTerminal
#print axioms MultiscaleTubeHierarchy.canonicalBufferedTestBodyChainOfNominalRadiusPosWithAutomaticTerminal

end
end FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
