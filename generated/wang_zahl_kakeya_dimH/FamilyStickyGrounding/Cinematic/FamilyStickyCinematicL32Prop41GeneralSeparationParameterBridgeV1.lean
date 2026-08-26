import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingY1ProducerV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory

namespace FamilyStickyCinematicL32Prop41GeneralSeparationParameterBridgeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingY1ProducerV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u

/-!
# The general Proposition 4.1 separation parameter

The unreduced PYZ Proposition 4.1 assumes separation at `t / A`, with
`A >= 1`; only its preliminary reduction later replaces this by separation
at a constant multiple of `t`.  For a radius-separated tube family at global
scale `t`, the faithful choice is therefore `A = t / radius`.

This adapter records that exact parameter choice.  It deliberately does not
claim the stronger `t`-separation used after the preliminary reduction.
-/

/-- The scale loss appearing in the unreduced Proposition 4.1 interface. -/
noncomputable def prop41SeparationLoss
    (radius globalScale : Real) : Real :=
  globalScale / radius

/-- If the global scale dominates the tube radius, the paper parameter
`A = globalScale / radius` is at least one. -/
theorem one_le_prop41SeparationLoss
    {radius globalScale : Real} (hradius : 0 < radius)
    (hradiusGlobalScale : radius <= globalScale) :
    1 <= prop41SeparationLoss radius globalScale := by
  rw [prop41SeparationLoss]
  exact (le_div_iff₀ hradius).2 (by simpa using hradiusGlobalScale)

/-- With the faithful loss parameter, the required separation scale `t / A`
is exactly the original tube radius. -/
theorem globalScale_div_prop41SeparationLoss
    {radius globalScale : Real} (hradius : 0 < radius)
    (hradiusGlobalScale : radius <= globalScale) :
    globalScale / prop41SeparationLoss radius globalScale = radius := by
  have hglobalScale : 0 < globalScale := hradius.trans_le hradiusGlobalScale
  rw [prop41SeparationLoss]
  field_simp [ne_of_gt hradius, ne_of_gt hglobalScale]

/-- Radius separation is precisely the general `t / A` separation required
before PYZ Lemma 4.3. -/
theorem prop41_generalSeparation_of_radiusSeparation
    {alpha : Type*} (distance : alpha -> alpha -> Real)
    {radius globalScale : Real} (hradius : 0 < radius)
    (hradiusGlobalScale : radius <= globalScale) {x y : alpha}
    (hseparated : radius <= distance x y) :
    globalScale / prop41SeparationLoss radius globalScale <= distance x y := by
  rw [globalScale_div_prop41SeparationLoss hradius hradiusGlobalScale]
  exact hseparated

/-- The literal positive-centre `Y1` image automatically satisfies the
unreduced Proposition 4.1 separation condition with
`A = globalScale / radius`. -/
theorem positiveCenterY1_activeTubeImage_pairwise_prop41Separated
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical :
      FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
        (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (tangencyExponent : Real) (tangencyLabel : Int) (q : Real × Real)
    (hradius : 0 < radius)
    (hradiusGlobalScale : (radius : Real) <= globalScale) :
    let Y1 := positiveCenterY1 base hbase fine physical f f1 f2 outerA
      outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
      tangencyLabel
    let A := prop41SeparationLoss (radius : Real) globalScale
    1 <= A ∧
      forall T, T ∈ activeTubeImage fine (Y1.activeAtPoint q) ->
        forall U, U ∈ activeTubeImage fine (Y1.activeAtPoint q) -> T ≠ U ->
          globalScale / A <= projectedTubePairCoefficientDistance T U := by
  dsimp only
  have hradiusReal : 0 < (radius : Real) := by exact_mod_cast hradius
  refine ⟨one_le_prop41SeparationLoss hradiusReal hradiusGlobalScale, ?_⟩
  intro T hT U hU hTU
  have hseparated :=
    positiveCenterY1_activeTubeImage_pairwise_radiusSeparated
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter tangencyExponent tangencyLabel q
      T hT U hU hTU
  exact prop41_generalSeparation_of_radiusSeparation
    projectedTubePairCoefficientDistance hradiusReal hradiusGlobalScale
      hseparated

#print axioms prop41SeparationLoss
#print axioms one_le_prop41SeparationLoss
#print axioms globalScale_div_prop41SeparationLoss
#print axioms prop41_generalSeparation_of_radiusSeparation
#print axioms positiveCenterY1_activeTubeImage_pairwise_prop41Separated

end

end FamilyStickyCinematicL32Prop41GeneralSeparationParameterBridgeV1
