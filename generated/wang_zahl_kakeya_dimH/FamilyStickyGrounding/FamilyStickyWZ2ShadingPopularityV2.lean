import FamilyStickyGrounding.FamilyStickyWZ2PopularFibersV1
import Submission.Kakeya.ConvexGeometry.Shading

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory

namespace FamilyStickyWZ2ShadingPopularityV2

open FamilyStickyWZ2PopularFibersV1
open Submission.Kakeya.ConvexGeometry
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# WZ2 popular fibers for an actual shading

This module is the measure-theoretic adapter for the finite popularity kernel
in `FamilyStickyWZ2PopularFibersV1`.  It formalizes the finite double count
used in Section 7 of Wang--Zahl, *The Assouad dimension of Kakeya sets in R3*:
the integral of the active tube multiplicity over a restricted set is the sum
of the restricted shading masses.  A lower bound for that integral then
retains many tubes with large restricted mass.

No projection theorem, geometric incidence estimate, or conclusion of WZ2
Theorem 5.2 is assumed here.
-/

variable {iota : Type*} {F : ConvexFamily iota}

/-- Multiplicity formed only from a specified finite set of family indices. -/
noncomputable def activePointMultiplicity
    (Y : Shading F) (active : Finset iota) (x : Space) : Nat := by
  classical
  exact (active.filter fun i => x ∈ Y.carrier i).card

/-- Shading mass of one family member after restriction to `X`. -/
noncomputable def restrictedMass
    (Y : Shading F) (X : Set Space) (i : iota) : ENNReal :=
  volume (Y.carrier i ∩ X)

/-- The finite real representative of one restricted shading mass. -/
noncomputable def restrictedMassReal
    (Y : Shading F) (X : Set Space) (i : iota) : Real :=
  (restrictedMass Y X i).toReal

/-- Actual shading indices whose restricted mass reaches the half-density
threshold from the finite popularity lemma. -/
noncomputable def popularRestrictedIndices
    (Y : Shading F) (active : Finset iota) (X : Set Space)
    (alpha cap : Real) : Finset iota :=
  popularIndices active (restrictedMassReal Y X) (alpha / 2 * cap)

/-- Active multiplicity is the finite sum of carrier indicators. -/
theorem activePointMultiplicity_cast_eq_sum_indicator
    (Y : Shading F) (active : Finset iota) (x : Space) :
    (activePointMultiplicity Y active x : ENNReal) =
      ∑ i ∈ active,
        (Y.carrier i).indicator (fun _ => (1 : ENNReal)) x := by
  classical
  simp [activePointMultiplicity, Set.indicator_apply]

/-- Exact finite double counting on a restricted set: integrating active
multiplicity over `X` equals summing the restricted mass of every active
shading piece. -/
theorem lintegral_activePointMultiplicity_restrict
    (Y : Shading F) (active : Finset iota) (X : Set Space) :
    (∫⁻ x in X, (activePointMultiplicity Y active x : ENNReal) ∂volume) =
      ∑ i ∈ active, restrictedMass Y X i := by
  classical
  simp_rw [activePointMultiplicity_cast_eq_sum_indicator]
  rw [lintegral_finsetSum active]
  · apply Finset.sum_congr rfl
    intro i hi
    unfold restrictedMass
    rw [setLIntegral_indicator (Y.measurable_carrier i), setLIntegral_one]
  · intro i hi
    exact measurable_const.indicator (Y.measurable_carrier i)

/-- Restriction cannot increase the mass of one shading piece. -/
theorem restrictedMass_le_carrierMass
    (Y : Shading F) (X : Set Space) (i : iota) :
    restrictedMass Y X i <= volume (Y.carrier i) := by
  exact measure_mono Set.inter_subset_left

/-- Every restricted mass is finite because the shading lies in a compact
convex body. -/
theorem restrictedMass_lt_top
    (Y : Shading F) (X : Set Space) (i : iota) :
    restrictedMass Y X i < ∞ := by
  exact (restrictedMass_le_carrierMass Y X i).trans_lt
    ((measure_mono (Y.carrier_subset i)).trans_lt
      (F i).isCompact.measure_lt_top)

/-- The real restricted mass is bounded by the real carrier mass. -/
theorem restrictedMassReal_le_carrierMassReal
    (Y : Shading F) (X : Set Space) (i : iota) :
    restrictedMassReal Y X i <= (volume (Y.carrier i)).toReal := by
  unfold restrictedMassReal
  exact ENNReal.toReal_mono
    (((measure_mono (Y.carrier_subset i)).trans_lt
      (F i).isCompact.measure_lt_top).ne)
    (restrictedMass_le_carrierMass Y X i)

/-- Real-valued form of the restricted double count. -/
theorem sum_restrictedMassReal_eq_lintegral_toReal
    (Y : Shading F) (active : Finset iota) (X : Set Space) :
    (∑ i ∈ active, restrictedMassReal Y X i) =
      (∫⁻ x in X,
        (activePointMultiplicity Y active x : ENNReal) ∂volume).toReal := by
  calc
    (∑ i ∈ active, restrictedMassReal Y X i) =
        (∑ i ∈ active, restrictedMass Y X i).toReal := by
      exact (ENNReal.toReal_sum fun i hi => (restrictedMass_lt_top Y X i).ne).symm
    _ = (∫⁻ x in X,
          (activePointMultiplicity Y active x : ENNReal) ∂volume).toReal := by
      rw [lintegral_activePointMultiplicity_restrict]

/-- Actual-shading popularity from a summed restricted-mass lower bound. -/
theorem half_density_card_le_popularRestricted_card_of_sum
    (Y : Shading F) (active : Finset iota) (X : Set Space)
    (alpha cap : Real) (halpha0 : 0 <= alpha) (hcap0 : 0 < cap)
    (hcarrierCap : forall i, i ∈ active ->
      (volume (Y.carrier i)).toReal <= cap)
    (hmass : alpha * active.card * cap <=
      ∑ i ∈ active, restrictedMassReal Y X i) :
    alpha / 2 * active.card <=
      (popularRestrictedIndices Y active X alpha cap).card := by
  unfold popularRestrictedIndices
  apply half_density_card_le_popular_card
      active (restrictedMassReal Y X) alpha cap halpha0 hcap0
  · intro i hi
    exact (restrictedMassReal_le_carrierMassReal Y X i).trans
      (hcarrierCap i hi)
  · exact hmass

/-- Source-shaped adapter: a lower bound on the restricted multiplicity
integral retains an `alpha / 2` fraction of the active shading indices. -/
theorem half_density_card_le_popularRestricted_card_of_lintegral
    (Y : Shading F) (active : Finset iota) (X : Set Space)
    (alpha cap : Real) (halpha0 : 0 <= alpha) (hcap0 : 0 < cap)
    (hcarrierCap : forall i, i ∈ active ->
      (volume (Y.carrier i)).toReal <= cap)
    (hmass : alpha * active.card * cap <=
      (∫⁻ x in X,
        (activePointMultiplicity Y active x : ENNReal) ∂volume).toReal) :
    alpha / 2 * active.card <=
      (popularRestrictedIndices Y active X alpha cap).card := by
  apply half_density_card_le_popularRestricted_card_of_sum
      Y active X alpha cap halpha0 hcap0 hcarrierCap
  rw [sum_restrictedMassReal_eq_lintegral_toReal]
  exact hmass

#print axioms activePointMultiplicity_cast_eq_sum_indicator
#print axioms lintegral_activePointMultiplicity_restrict
#print axioms restrictedMass_le_carrierMass
#print axioms restrictedMass_lt_top
#print axioms restrictedMassReal_le_carrierMassReal
#print axioms sum_restrictedMassReal_eq_lintegral_toReal
#print axioms half_density_card_le_popularRestricted_card_of_sum
#print axioms half_density_card_le_popularRestricted_card_of_lintegral

end

end FamilyStickyWZ2ShadingPopularityV2
