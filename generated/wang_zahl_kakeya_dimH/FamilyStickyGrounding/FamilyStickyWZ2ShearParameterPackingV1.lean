import FamilyStickyGrounding.FamilyStickyWZ2ReducedParameterClusterWindowV1
import FamilyStickyGrounding.FamilyStickyDenseLatticeBoxPointCountV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace FamilyStickyWZ2ShearParameterPackingV1

open FamilyStickyWZ2CinematicTranslationV1
open FamilyStickyDenseLatticeBoxPointCountV1
open FamilyStickyWZ2ReducedParameterClusterWindowV1

noncomputable section

/-!
# Explicit finite packing in the genuine WZ2 shear parameter

The copy sites vary in the reduced `d` coordinate.  Under WZ2's ambient
action this is the height-dependent shear `y -> y + d*z`.  A residue-class
injection proves an exact local grid count.  The cluster-to-window theorem
then replaces the global copy factor by a local ceiling budget.
-/

/-- Literal finite grid in the reduced `d` (ambient shear) coordinate. -/
def shearReducedShift (spacing : Real) {siteCount : Nat}
    (j : Fin siteCount) : ReducedLineParameter :=
  (0, (0, ((j : Nat) : Real) * spacing))

/-- Canonical interval-count budget for a shear grid meeting a window. -/
def shearShiftHitBudget (spacing radius : Real) : Nat :=
  Nat.ceil ((2 * radius) / spacing) + 1

theorem shearShiftHitBudget_pos (spacing radius : Real) :
    0 < shearShiftHitBudget spacing radius := by
  simp [shearShiftHitBudget]

theorem two_mul_radius_lt_shearShiftHitBudget_mul_spacing
    {spacing radius : Real} (hspacing : 0 < spacing) :
    2 * radius < (shearShiftHitBudget spacing radius : Real) * spacing := by
  have hceil :
      (2 * radius) / spacing <=
        (Nat.ceil ((2 * radius) / spacing) : Real) := Nat.le_ceil _
  have hbase :
      2 * radius <=
        (Nat.ceil ((2 * radius) / spacing) : Real) * spacing :=
    (div_le_iff₀ hspacing).mp hceil
  simp only [shearShiftHitBudget, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- Two shear-grid sites in the same parameter window have lattice
separation at most twice the window radius. -/
theorem abs_shear_site_sub_mul_le_two_radius
    {spacing radius : Real} {siteCount : Nat}
    (center : ReducedLineParameter) {j k : Fin siteCount}
    (hj : reducedParameterDistance (shearReducedShift spacing j) center <=
      radius)
    (hk : reducedParameterDistance (shearReducedShift spacing k) center <=
      radius) :
    |(((j : Nat) : Real) - ((k : Nat) : Real)) * spacing| <=
      2 * radius := by
  have hj' :=
    (abs_snd_snd_sub_le_reducedParameterDistance
      (shearReducedShift spacing j) center).trans hj
  have hk' :=
    (abs_snd_snd_sub_le_reducedParameterDistance
      (shearReducedShift spacing k) center).trans hk
  calc
    |(((j : Nat) : Real) - ((k : Nat) : Real)) * spacing| =
        |((((j : Nat) : Real) * spacing - center.2.2) -
          (((k : Nat) : Real) * spacing - center.2.2))| := by
        congr 1
        ring
    _ <= |((j : Nat) : Real) * spacing - center.2.2| +
        |((k : Nat) : Real) * spacing - center.2.2| := abs_sub _ _
    _ <= radius + radius := add_le_add
      (by simpa [shearReducedShift] using hj')
      (by simpa [shearReducedShift] using hk')
    _ = 2 * radius := by ring

/-- Exact local count for the finite shear grid, produced by injection into
explicit modular residue classes. -/
theorem card_shearReducedShift_window_le_hitBudget
    {siteCount : Nat} {spacing radius : Real}
    (hspacing : 0 < spacing) (hradius : 0 <= radius)
    (center : ReducedLineParameter) :
    (parameterWindowIndices
      (shearReducedShift spacing (siteCount := siteCount)) center radius).card <=
      shearShiftHitBudget spacing radius := by
  classical
  let hits : Finset (Fin siteCount) :=
    parameterWindowIndices
      (shearReducedShift spacing (siteCount := siteCount)) center radius
  let residue : {j // j ∈ hits} -> Fin (shearShiftHitBudget spacing radius) :=
    fun j =>
      ⟨(j.1 : Nat) % shearShiftHitBudget spacing radius,
        Nat.mod_lt _ (shearShiftHitBudget_pos spacing radius)⟩
  have hinjective : Function.Injective residue := by
    intro j k heq
    apply Subtype.ext
    apply Fin.ext
    apply nat_eq_of_mod_eq_of_abs_cast_sub_mul_le
      (shearShiftHitBudget_pos spacing radius) (by positivity)
      (two_mul_radius_lt_shearShiftHitBudget_mul_spacing hspacing)
    · exact congrArg Fin.val heq
    · apply abs_shear_site_sub_mul_le_two_radius center
      · exact (Finset.mem_filter.mp j.2).2
      · exact (Finset.mem_filter.mp k.2).2
  have hcard := Fintype.card_le_of_injective residue hinjective
  simpa only [hits, Fintype.card_coe, Fintype.card_fin] using hcard

/-- Product-family occupancy for actual `d`-shear copy parameters.  Its copy
factor is local and independent of the total site count. -/
theorem card_shearGrid_translatedParameterWindow_le
    {siteCount : Nat} {kappa : Type*}
    [Fintype kappa] [DecidableEq kappa]
    (parameter : kappa -> ReducedLineParameter)
    (base center : ReducedLineParameter)
    {spacing rho radius : Real}
    (hspacing : 0 < spacing) (hrho : 0 <= rho) (hradius : 0 <= radius)
    (hcluster : forall i,
      reducedParameterDistance (parameter i) base <= rho) :
    (translatedParameterWindowIndices
      (shearReducedShift spacing (siteCount := siteCount))
      parameter center radius).card <=
      Fintype.card kappa * shearShiftHitBudget spacing (radius + rho) := by
  calc
    (translatedParameterWindowIndices
      (shearReducedShift spacing (siteCount := siteCount))
      parameter center radius).card <=
        Fintype.card kappa *
          (parameterWindowIndices
            (shearReducedShift spacing (siteCount := siteCount))
            (reducedParameterSub center base) (radius + rho)).card :=
      card_translatedParameterWindowIndices_le_card_mul_shiftWindow
        (shearReducedShift spacing (siteCount := siteCount)) parameter
        base center hcluster
    _ <= Fintype.card kappa *
        shearShiftHitBudget spacing (radius + rho) := by
      gcongr
      exact card_shearReducedShift_window_le_hitBudget hspacing
        (add_nonneg hradius hrho) (reducedParameterSub center base)

/-- Honest improvement envelope: the copy factor is the minimum of the total
copy count and the explicit local shear-grid budget. -/
theorem card_shearGrid_translatedParameterWindow_le_min
    {siteCount : Nat} {kappa : Type*}
    [Fintype kappa] [DecidableEq kappa]
    (parameter : kappa -> ReducedLineParameter)
    (base center : ReducedLineParameter)
    {spacing rho radius : Real}
    (hspacing : 0 < spacing) (hrho : 0 <= rho) (hradius : 0 <= radius)
    (hcluster : forall i,
      reducedParameterDistance (parameter i) base <= rho) :
    (translatedParameterWindowIndices
      (shearReducedShift spacing (siteCount := siteCount))
      parameter center radius).card <=
      Fintype.card kappa *
        min siteCount (shearShiftHitBudget spacing (radius + rho)) := by
  rw [mul_min]
  apply Nat.le_min.mpr
  constructor
  · calc
      (translatedParameterWindowIndices
        (shearReducedShift spacing (siteCount := siteCount))
        parameter center radius).card <=
          Fintype.card (Fin siteCount × kappa) := by
        simpa [translatedParameterWindowIndices] using
          Finset.card_filter_le (Finset.univ : Finset (Fin siteCount × kappa))
            (fun ji => reducedParameterDistance
              (translateReducedLineParameter
                (shearReducedShift spacing ji.1).1
                (shearReducedShift spacing ji.1).2.1
                (shearReducedShift spacing ji.1).2.2
                (parameter ji.2)) center <= radius)
      _ = Fintype.card kappa * siteCount := by simp [Nat.mul_comm]
  · exact card_shearGrid_translatedParameterWindow_le parameter base center
      hspacing hrho hradius hcluster

#print axioms shearShiftHitBudget_pos
#print axioms two_mul_radius_lt_shearShiftHitBudget_mul_spacing
#print axioms abs_shear_site_sub_mul_le_two_radius
#print axioms card_shearReducedShift_window_le_hitBudget
#print axioms card_shearGrid_translatedParameterWindow_le
#print axioms card_shearGrid_translatedParameterWindow_le_min

end
end FamilyStickyWZ2ShearParameterPackingV1
