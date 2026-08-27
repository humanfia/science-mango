import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SampledLensPaperShapeNumericsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41FiniteRandomSamplingLensAssemblyV1

open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SampledLensPaperShapeNumericsV1

noncomputable section

/-!
# The complete finite random-sampling reduction for Proposition 4.1

The properly-intersecting lens estimate only needs one sampled curve from
each side of every surviving rectangle.  Independent uniform colourings
retain at least one eighth of all rectangles while their total zero-colour
load is at most seven times

|left| / mu + |right| / nu.

This file performs the final deterministic composition.  Thus the general
mu/nu reduction no longer remains hidden behind the paper's citation of a
"standard random sampling argument".
-/

/-- Abstract endpoint of the two-sided random-sampling reduction.  The input
hsampledLens is precisely the one-hit lens estimate on each concrete sampled
outcome; the conclusion is the corresponding general mu/nu bound. -/
theorem rectangleCard_le_eight_mul_sampledLensBound_of_twoSidedSampling
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (hleft : forall R, mu <= (leftNeighbors R).card)
    (hright : forall R, nu <= (rightNeighbors R).card)
    (depth : Real) (hdepth : 0 <= depth)
    (hsampledLens : forall omega :
        (alpha -> Fin mu) × (beta -> Fin nu),
      ((twoSidedZeroColorSurvivors mu nu leftNeighbors rightNeighbors
          omega).card : Real) <=
        sampledLensBound depth (twoSidedZeroColorLoad mu nu omega)) :
    (Fintype.card Rectangle : Real) <=
      8 * sampledLensBound depth
        (7 * ((Fintype.card alpha : Real) / (mu : Real) +
          (Fintype.card beta : Real) / (nu : Real))) := by
  obtain ⟨omega, hsurvival, hload⟩ :=
    exists_twoSidedZeroColor_sample_with_eighth_survival_and_sevenfold_load
      mu nu leftNeighbors rightNeighbors hleft hright
  exact rectangleCount_le_eight_mul_sampledLensBound
    hdepth (twoSidedZeroColorLoad_nonneg mu nu omega)
      hsurvival (hsampledLens omega) hload

/-- Paper-shaped version of the complete reduction. -/
theorem rectangleCard_le_sampledLensPaperShape_of_twoSidedSampling
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (hleft : forall R, mu <= (leftNeighbors R).card)
    (hright : forall R, nu <= (rightNeighbors R).card)
    (depth : Real) (hdepth : 0 <= depth)
    (hsampledLens : forall omega :
        (alpha -> Fin mu) × (beta -> Fin nu),
      ((twoSidedZeroColorSurvivors mu nu leftNeighbors rightNeighbors
          omega).card : Real) <=
        sampledLensBound depth (twoSidedZeroColorLoad mu nu omega))
    (hbudget : 1 <=
      7 * ((Fintype.card alpha : Real) / (mu : Real) +
        (Fintype.card beta : Real) / (nu : Real))) :
    (Fintype.card Rectangle : Real) <=
      8 * (316 + 48 * depth) *
        (7 * ((Fintype.card alpha : Real) / (mu : Real) +
          (Fintype.card beta : Real) / (nu : Real))) *
        Real.sqrt
          (7 * ((Fintype.card alpha : Real) / (mu : Real) +
            (Fintype.card beta : Real) / (nu : Real))) := by
  let load : Real :=
    7 * ((Fintype.card alpha : Real) / (mu : Real) +
      (Fintype.card beta : Real) / (nu : Real))
  have hbase : (Fintype.card Rectangle : Real) <=
      8 * sampledLensBound depth load := by
    simpa only [load] using
      rectangleCard_le_eight_mul_sampledLensBound_of_twoSidedSampling
        mu nu leftNeighbors rightNeighbors hleft hright depth hdepth
          hsampledLens
  have hshape : sampledLensBound depth load <=
      (316 + 48 * depth) * load * Real.sqrt load :=
    sampledLensBound_le_paperShape (by simpa only [load] using hbudget)
  calc
    (Fintype.card Rectangle : Real) <=
        8 * sampledLensBound depth load := hbase
    _ <= 8 * ((316 + 48 * depth) * load * Real.sqrt load) :=
      mul_le_mul_of_nonneg_left hshape (by norm_num)
    _ = 8 * (316 + 48 * depth) * load * Real.sqrt load := by ring
    _ = _ := by rfl

/-- The paper-shaped load lower bound is automatic.  If there are no
rectangles the conclusion is trivial; otherwise one rectangle and the two
neighbour-cardinality hypotheses show that each normalized ambient size is
at least one. -/
theorem rectangleCard_le_sampledLensPaperShape_of_twoSidedSampling_automaticBudget
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (hleft : forall R, mu <= (leftNeighbors R).card)
    (hright : forall R, nu <= (rightNeighbors R).card)
    (depth : Real) (hdepth : 0 <= depth)
    (hsampledLens : forall omega :
        (alpha -> Fin mu) × (beta -> Fin nu),
      ((twoSidedZeroColorSurvivors mu nu leftNeighbors rightNeighbors
          omega).card : Real) <=
        sampledLensBound depth (twoSidedZeroColorLoad mu nu omega)) :
    (Fintype.card Rectangle : Real) <=
      8 * (316 + 48 * depth) *
        (7 * ((Fintype.card alpha : Real) / (mu : Real) +
          (Fintype.card beta : Real) / (nu : Real))) *
        Real.sqrt
          (7 * ((Fintype.card alpha : Real) / (mu : Real) +
            (Fintype.card beta : Real) / (nu : Real))) := by
  by_cases hRectangle : Fintype.card Rectangle = 0
  · rw [hRectangle]
    norm_num only [Nat.cast_zero]
    have hshapeNonneg : 0 <= 316 + 48 * depth := by
      nlinarith
    have hloadNonneg : 0 <=
        7 * ((Fintype.card alpha : Real) / (mu : Real) +
          (Fintype.card beta : Real) / (nu : Real)) := by
      positivity
    have heightNonneg : (0 : Real) <= 8 := by
      norm_num
    exact mul_nonneg
      (mul_nonneg (mul_nonneg heightNonneg hshapeNonneg) hloadNonneg)
      (Real.sqrt_nonneg
        (7 * ((Fintype.card alpha : Real) / (mu : Real) +
          (Fintype.card beta : Real) / (nu : Real))))
  have hRectanglePos : 0 < Fintype.card Rectangle :=
    Nat.pos_of_ne_zero hRectangle
  let R : Rectangle := Classical.choice
    (Fintype.card_pos_iff.mp hRectanglePos)
  have hmuCardNat : mu <= Fintype.card alpha :=
    (hleft R).trans (Finset.card_le_univ (leftNeighbors R))
  have hnuCardNat : nu <= Fintype.card beta :=
    (hright R).trans (Finset.card_le_univ (rightNeighbors R))
  have hmuPosNat : 0 < mu := Nat.pos_of_ne_zero (NeZero.ne mu)
  have hnuPosNat : 0 < nu := Nat.pos_of_ne_zero (NeZero.ne nu)
  have hmuPos : (0 : Real) < mu := by exact_mod_cast hmuPosNat
  have hnuPos : (0 : Real) < nu := by exact_mod_cast hnuPosNat
  have hmuCard : (mu : Real) <= Fintype.card alpha := by
    exact_mod_cast hmuCardNat
  have hnuCard : (nu : Real) <= Fintype.card beta := by
    exact_mod_cast hnuCardNat
  have hleftRatio : (1 : Real) <=
      (Fintype.card alpha : Real) / (mu : Real) := by
    exact (le_div_iff₀ hmuPos).2 (by simpa using hmuCard)
  have hrightRatio : (1 : Real) <=
      (Fintype.card beta : Real) / (nu : Real) := by
    exact (le_div_iff₀ hnuPos).2 (by simpa using hnuCard)
  apply rectangleCard_le_sampledLensPaperShape_of_twoSidedSampling
    mu nu leftNeighbors rightNeighbors hleft hright depth hdepth
      hsampledLens
  nlinarith

#print axioms rectangleCard_le_eight_mul_sampledLensBound_of_twoSidedSampling
#print axioms rectangleCard_le_sampledLensPaperShape_of_twoSidedSampling
#print axioms rectangleCard_le_sampledLensPaperShape_of_twoSidedSampling_automaticBudget

end

end FamilyStickyCinematicL32Prop41FiniteRandomSamplingLensAssemblyV1
