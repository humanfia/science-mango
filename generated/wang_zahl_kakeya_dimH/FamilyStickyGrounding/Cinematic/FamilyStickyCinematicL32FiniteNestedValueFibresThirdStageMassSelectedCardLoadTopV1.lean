import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassSelectedCardTopV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassSelectedCardLoadTopV1

open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassSelectedCardTopV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1

noncomputable section

universe u v

/-!
# Outer third-stage mass aggregation with a deterministic curve load

The dependent per-value third-stage outcomes have already been reduced to
their selected cardinalities.  This final numerical adapter replaces the
literal global curve carrier by any larger real load without changing the
depth chosen uniformly for all fibres.
-/

/-- Replace the literal global-curve cardinality in the dependent
selected-cardinality mass top by any deterministic upper load. -/
theorem mass_le_local_mul_third_mul_sampledLensBound_load_mul_cap_of_selectedCard
    {value : Type u} {curve : Type v} [DecidableEq curve]
    (totalMass : ENNReal) (values : Finset value)
    (massAt : value -> ENNReal) (selectedCard : value -> Nat)
    (localPacking thirdPacking cap : ENNReal)
    (curveFiber : value -> Finset curve) (globalCurves : Finset curve)
    (depth load : Real) (hdepth : 0 <= depth)
    (hpartition : totalMass <= ∑ c ∈ values, massAt c)
    (hfibre : forall c, c ∈ values ->
      massAt c <= localPacking * thirdPacking *
        (selectedCard c : ENNReal) * cap)
    (hcurveDisjoint : (values : Set value).PairwiseDisjoint curveFiber)
    (hcurveSubset : values.biUnion curveFiber ⊆ globalCurves)
    (hglobalLoad : (globalCurves.card : Real) <= load)
    (hselected : forall c, c ∈ values ->
      ((selectedCard c : Nat) : Real) <=
        sampledLensBound depth ((curveFiber c).card : Real)) :
    totalMass <= localPacking * thirdPacking *
      ENNReal.ofReal (sampledLensBound depth load) * cap := by
  have hbase : totalMass <= localPacking * thirdPacking *
      ENNReal.ofReal
        (sampledLensBound depth (globalCurves.card : Real)) * cap :=
    mass_le_local_mul_third_mul_sampledLensBound_mul_cap_of_selectedCard
      totalMass values massAt selectedCard localPacking thirdPacking cap
        curveFiber globalCurves depth hdepth hpartition hfibre
          hcurveDisjoint hcurveSubset hselected
  have hmono : sampledLensBound depth (globalCurves.card : Real) <=
      sampledLensBound depth load :=
    sampledLensBound_mono_curveCount hdepth (Nat.cast_nonneg _) hglobalLoad
  calc
    totalMass <= localPacking * thirdPacking *
        ENNReal.ofReal
          (sampledLensBound depth (globalCurves.card : Real)) * cap := hbase
    _ <= localPacking * thirdPacking *
        ENNReal.ofReal (sampledLensBound depth load) * cap := by
      gcongr

#print axioms mass_le_local_mul_third_mul_sampledLensBound_load_mul_cap_of_selectedCard

end

end FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassSelectedCardLoadTopV1
