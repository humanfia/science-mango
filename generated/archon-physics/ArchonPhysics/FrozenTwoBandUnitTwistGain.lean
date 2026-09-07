import ArchonPhysics.FiniteUnitTwistHypercubeCancellation
import ArchonPhysics.RandomMassPhaseInitialData

/-!
# Frozen two-band gains for Boolean unit-twist sums

The frozen v0.3 initial profile assigns at most `3 / (N - 1)` energy to each
positive ordered mode and zero to the translation mode.  Consequently, the
difference between the energies of any two ordered modes has the same
`O(1 / N)` bound.  A Boolean product-difference class with `q` independent
twists therefore gains the `q`-th power of that bound.

This is the profile factor in a Deng--Hani/Vassilev--Wu style twist estimate.
It does not assert that actual random-mass FPUT decorated couples form such a
Boolean orbit, nor that their remaining interaction, phase, and time factors
are invariant under a twist.
-/

namespace ArchonPhysics.FrozenTwoBandUnitTwistGain

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.FiniteUnitTwistHypercubeCancellation
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TwoBandInitialEnergyProfile

noncomputable section

variable {Twist : Type*}

/-- Every frozen ordered-mode energy, including the zero translation mode,
is bounded by the same inverse-volume envelope. -/
theorem orderedTargetEnergy_le_three_div_pred
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (mode : OrderedModeIndex N) :
    orderedTargetEnergy N a mode <=
      3 / (((N - 1 : Nat) : Real)) := by
  unfold orderedTargetEnergy orderedPositiveInitialEnergyProfile
  split_ifs with hmode
  · exact initialEnergyProfile_le_three_div
      (M := N - 1) (by omega) ha0 ha1 _
  · positivity

/-- Any two frozen ordered-mode energies differ by at most the one-mode
inverse-volume envelope.  No adjacency or Fourier momentum is needed. -/
theorem abs_orderedTargetEnergy_sub_le_three_div_pred
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (left right : OrderedModeIndex N) :
    |orderedTargetEnergy N a left - orderedTargetEnergy N a right| <=
      3 / (((N - 1 : Nat) : Real)) := by
  have hleftNonneg : 0 <= orderedTargetEnergy N a left :=
    orderedPositiveInitialEnergyProfile_nonneg
      hN ha0 ha1 (orderedModeIndexEquivFin N left)
  have hrightNonneg : 0 <= orderedTargetEnergy N a right :=
    orderedPositiveInitialEnergyProfile_nonneg
      hN ha0 ha1 (orderedModeIndexEquivFin N right)
  have hleftUpper :=
    orderedTargetEnergy_le_three_div_pred hN ha0 ha1 left
  have hrightUpper :=
    orderedTargetEnergy_le_three_div_pred hN ha0 ha1 right
  rw [abs_le]
  constructor <;> linarith

/-- A product of `q` frozen-energy differences gains the `q`-th power of
the inverse-volume envelope. -/
theorem prod_abs_orderedTargetEnergy_sub_le
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (twists : Finset Twist)
    (left right : Twist -> OrderedModeIndex N) :
    (∏ twist ∈ twists,
      |orderedTargetEnergy N a (left twist) -
        orderedTargetEnergy N a (right twist)|) <=
      (3 / (((N - 1 : Nat) : Real))) ^ twists.card := by
  calc
    (∏ twist ∈ twists,
        |orderedTargetEnergy N a (left twist) -
          orderedTargetEnergy N a (right twist)|) <=
        ∏ _twist ∈ twists,
          (3 / (((N - 1 : Nat) : Real))) := by
      apply Finset.prod_le_prod
      · intro twist _htwist
        exact abs_nonneg _
      · intro twist _htwist
        exact abs_orderedTargetEnergy_sub_le_three_div_pred
          hN ha0 ha1 (left twist) (right twist)
    _ = (3 / (((N - 1 : Nat) : Real))) ^ twists.card := by
      simp only [Finset.prod_const]

/-- The complete Boolean alternating product made from frozen mode energies
inherits the multiplicative inverse-volume gain.  Connecting an actual FPUT
twist class to this expression remains a separate model theorem. -/
theorem norm_frozenEnergy_unitTwistHypercubeSum_le
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    [DecidableEq Twist]
    (twists : Finset Twist)
    (left right : Twist -> OrderedModeIndex N) :
    ‖unitTwistHypercubeSum twists
        (unitTwistAlternatingProductTerm twists
          (fun twist => orderedTargetEnergy N a (left twist))
          (fun twist => orderedTargetEnergy N a (right twist)))‖ <=
      (3 / (((N - 1 : Nat) : Real))) ^ twists.card := by
  exact
    (norm_unitTwistHypercubeSum_alternatingProduct_le
      twists
      (fun twist => orderedTargetEnergy N a (left twist))
      (fun twist => orderedTargetEnergy N a (right twist))).trans
      (by
        simpa only [Real.norm_eq_abs] using
          prod_abs_orderedTargetEnergy_sub_le
            hN ha0 ha1 twists left right)

end

end ArchonPhysics.FrozenTwoBandUnitTwistGain
