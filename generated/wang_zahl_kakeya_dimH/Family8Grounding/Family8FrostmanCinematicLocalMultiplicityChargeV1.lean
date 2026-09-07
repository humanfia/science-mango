import Family8Grounding.Family8FrostmanCinematicFirstHitMassDecompositionV1
import Submission.Kakeya.ConvexFactoring.MultiplicityPigeonhole

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FrostmanCinematicLocalMultiplicityChargeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8FrostmanCinematicFirstHitMassDecompositionV1
open FamilyStickyWZ2ShadingPopularityV2
open FamilyStickyCinematicL32Lemma55FiniteMeasurableFirstHitPartitionV1

noncomputable section

/-!
# Local cinematic charge from the literal point multiplicity

The multiplicity-counted mass assigned to a spatial cell is exactly the
restricted integral of the original shading's point multiplicity.  Hence a
genuine pointwise multiplicity cap on a cell produces the local charge used
by the first-hit global argument.  This is an upstream geometric premise,
not a restatement of the desired integral inequality.

The final theorem reduces the remaining Family 7 input to pointwise bounds
on the automatically constructed first-hit cells.
-/

/-- The WZ2 active multiplicity on the full finite family is the native
`Shading.pointMultiplicity`. -/
theorem activePointMultiplicity_univ_eq_pointMultiplicity
    {iota : Type} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F) (x : Space) :
    activePointMultiplicity Y (Finset.univ : Finset iota) x =
      Y.pointMultiplicity x := by
  rfl

/-- Exact restricted first moment on one literal spatial cell. -/
theorem cellRestrictedShadingMass_eq_setLIntegral_pointMultiplicity
    {iota : Type} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F) (X : Set Space) :
    cellRestrictedShadingMass Y X =
      ∫⁻ x in X, (Y.pointMultiplicity x : ENNReal) ∂volume := by
  calc
    cellRestrictedShadingMass Y X =
        ∑ i ∈ (Finset.univ : Finset iota), restrictedMass Y X i := by
      simp [cellRestrictedShadingMass]
    _ = ∫⁻ x in X,
          (activePointMultiplicity Y (Finset.univ : Finset iota) x : ENNReal) ∂volume :=
      (lintegral_activePointMultiplicity_restrict Y (Finset.univ : Finset iota) X).symm
    _ = ∫⁻ x in X, (Y.pointMultiplicity x : ENNReal) ∂volume := by
      congr 1

/-- A literal pointwise multiplicity cap controls the multiplicity-counted
mass of the same cell. -/
theorem cellRestrictedShadingMass_le_cap_mul_volume
    {iota : Type} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F) (X : Set Space)
    (cap : ENNReal)
    (hcap : forall x, x ∈ X -> (Y.pointMultiplicity x : ENNReal) <= cap) :
    cellRestrictedShadingMass Y X <= cap * volume X := by
  rw [cellRestrictedShadingMass_eq_setLIntegral_pointMultiplicity]
  calc
    (∫⁻ x in X, (Y.pointMultiplicity x : ENNReal) ∂volume) <=
        ∫⁻ _x in X, cap ∂volume := by
      exact setLIntegral_mono measurable_const hcap
    _ = cap * volume X := setLIntegral_const X cap

/-- On an exact native multiplicity slice, the local charge is exactly its
constant multiplicity times its volume. -/
theorem cellRestrictedShadingMass_multiplicitySlice
    {iota : Type} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F) (n : Nat) :
    cellRestrictedShadingMass Y (multiplicitySlice Y n) =
      (n : ENNReal) * volume (multiplicitySlice Y n) := by
  change (Y.restrictMultiplicitySlice n).shadingMass =
    (n : ENNReal) * volume (multiplicitySlice Y n)
  exact Y.shadingMass_restrictMultiplicitySlice n

/-- The first-hit global union theorem with the local integral premise
replaced by a genuine pointwise cap on every actual spatial fibre. -/
theorem shadedUnion_lower_of_firstHit_pointMultiplicity_caps
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    {eta zeta gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hdensity : (delta : ENNReal) ^ eta <= D.shading.shadingDensity)
    (hfamily : (delta : ENNReal) ^ eta <= D.actualFamilyVolume)
    (hexponent : 2 * eta + zeta <= gamma / 2)
    {cell : Type} [DecidableEq cell]
    (cells : Finset cell) (event : cell -> Set Space)
    (hmeasurable : forall c, c ∈ cells -> MeasurableSet (event c))
    (hcover : forall x, x ∈ D.shading.shadedUnion ->
      exists c, c ∈ cells ∧ x ∈ event c)
    (hcap : forall c, c ∈ cells -> forall x,
      x ∈ finiteFirstHitFiber D.shading.shadedUnion cells event c ->
        (D.shading.pointMultiplicity x : ENNReal) <=
          (delta : ENNReal) ^ (-zeta)) :
    (delta : ENNReal) ^ (gamma / 2) <=
      volume D.shading.shadedUnion := by
  apply shadedUnion_lower_of_firstHit_cinematic_cell_charges
    D hdelta hdeltaOne hdensity hfamily hexponent cells event hmeasurable
      hcover
  intro c hc
  exact cellRestrictedShadingMass_le_cap_mul_volume D.shading _ _
    (hcap c hc)

#print axioms activePointMultiplicity_univ_eq_pointMultiplicity
#print axioms cellRestrictedShadingMass_eq_setLIntegral_pointMultiplicity
#print axioms cellRestrictedShadingMass_le_cap_mul_volume
#print axioms cellRestrictedShadingMass_multiplicitySlice
#print axioms shadedUnion_lower_of_firstHit_pointMultiplicity_caps

end

end Family8FrostmanCinematicLocalMultiplicityChargeV1
