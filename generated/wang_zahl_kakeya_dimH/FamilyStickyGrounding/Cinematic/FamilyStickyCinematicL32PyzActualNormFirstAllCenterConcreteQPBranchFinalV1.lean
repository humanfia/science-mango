import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchLowV5D

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterConcreteQPBranchFinalV1

open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchLowV5D
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4

noncomputable section

universe u

/-!
# Native high/low dichotomy with concrete Q/P retained

The frozen canonical-payload split selects either the high half or the low
half.  On the high side this successor exposes the literal local `Q/P`
witnesses and their rebuilt half-mass sum; it never returns to the older
independently chosen scalar right-hand side.  The low side is the existing
summed moment conclusion on the same frozen branch core.
-/

theorem actualAllCenter_nativeHighConcreteQP_or_lowMoment
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (G : NativeHighGeometry D) (L : NativeLowGeometry D) :
    NativeHighConcreteQPOutcome D G \/ L.Outcome := by
  rcases D.payloadAt_spec with
    ⟨_hpartition, hhalf, _hhigh, _hlow⟩
  rcases hhalf with hhalfHigh | hhalfLow
  · exact Or.inl (nativeHighConcreteQPOutcome_of_half D G hhalfHigh)
  · exact Or.inr (nativeLowOutcome_of_half D L hhalfLow)

#print axioms actualAllCenter_nativeHighConcreteQP_or_lowMoment

end
end FamilyStickyCinematicL32PyzActualNormFirstAllCenterConcreteQPBranchFinalV1
