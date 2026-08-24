import FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
import FamilyStickyCinematicL32ActualTubeIndexedCoefficientSelectionV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32ActualTubeIndexedCoefficientSelectionV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1

noncomputable section

/-!
# Actual Tube critical family on a projected multiplicity slice

The critical family at a projected point is the existing maximal
coefficient-separated selection of the literal active Tube image.  Its
nonemptiness is now produced from the multiplicity-band lower endpoint and
the already frozen local coefficient-fibre cap; it is not a pointwise input.
-/

universe u v

/-- Actual finite Tube family fed into both critical maximizers. -/
noncomputable def actualProjectedCriticalFamily
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota) :
    Finset (Tube delta) :=
  selectedTubes (activeTubeImage fine active) (delta : Real)

/-- The norm-distance table is independent of the finite incidence pattern,
but is packaged in the common pattern-indexed interface. -/
def actualProjectedNormDistance
    {delta : NNReal} {iota : Type u}
    (_active : Finset iota) : Tube delta → Tube delta → Real :=
  projectedTubePairCoefficientDistance

/-- The actual tangency-distance table in the common pattern-indexed
interface. -/
noncomputable def actualProjectedTangencyDistance
    {delta : NNReal} {iota : Type u}
    (f f1 f2 : Real → Real) (A B : Real) (hAB : A ≤ B)
    (hfDeriv : ∀ z, z ∈ Icc A B → HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, z ∈ Icc A B → HasDerivAt f1 (f2 z) z)
    (_active : Finset iota) : Tube delta → Tube delta → Real :=
  fun T U => projectedTubePairTangencyDistance T U f f1 f2 A B hAB
    hfDeriv hf1Deriv

/-- The lower multiplicity band and the actual local coefficient cap produce
nonemptiness of the selected critical family at every source point. -/
theorem actualProjectedCriticalFamily_nonempty_on_multiplicityBand
    {point : Type v} [MeasurableSpace point]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (Z : FiniteProjectedShading point iota)
    {lower upper multiplicity : Nat}
    (hdelta : 0 < delta) (hmultiplicity : 0 < multiplicity)
    (hlower : 3 * multiplicity ≤ lower)
    (hpair : ∀ x, x ∈ Z.multiplicityBand lower upper →
      Set.Pairwise (Z.activeAtPoint x : Set iota) fun i j =>
        EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (hactiveCap : ∀ x, x ∈ Z.multiplicityBand lower upper →
      ∀ center,
        center ∈ actualProjectedCriticalFamily fine (Z.activeAtPoint x) →
        (activeNearCoefficientIndices fine (Z.activeAtPoint x) center
          (delta : Real)).card ≤ multiplicity) :
    ∀ x, x ∈ Z.multiplicityBand lower upper →
      (actualProjectedCriticalFamily fine (Z.activeAtPoint x)).Nonempty := by
  intro x hx
  have hlarge : 3 * multiplicity ≤ (Z.activeAtPoint x).card :=
    hlower.trans (Z.mem_multiplicityBand.mp hx).2.1
  exact selectedTubes_nonempty_of_active_cap fine (Z.activeAtPoint x)
    hdelta (hpair x hx) hmultiplicity hlarge (hactiveCap x hx)

#print axioms actualProjectedCriticalFamily
#print axioms actualProjectedNormDistance
#print axioms actualProjectedTangencyDistance
#print axioms actualProjectedCriticalFamily_nonempty_on_multiplicityBand

end


end FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
