import ArchonPhysics.CanonicalIIDCoerciveMatchedDenominatorForestRank

/-!
# Corrected structural-rank adapter for the second-Picard RPA square

The legacy all-order cutoff bridge asks for an inequality between an
independent-denominator loss and an arithmetic interaction-pair count.  The
sharp order-two counterexample in
`CanonicalIIDCoerciveMatchedDenominatorForestRank` shows that this inequality
does not follow from Haar charge matching.  A repository audit finds no
higher-order RPA criterion that actually consumes that bridge: its only
downstream consumer is the corresponding legacy example file.

This module supplies the minimal replacement needed at physical second
Picard order.  It uses the already computed structural forest ranks

* three for iterated/iterated,
* two for either mixed orientation, and
* one for direct/direct,

without an independent-rank premise.  The single cutoff exponent `5 / 4`
closes both rank-two mixed and rank-one direct `g^4` sectors at the existing
quadratic kinetic deficit.  Rank-three iterated/iterated is separated as an
exact cancellation/renormalization remainder; the absolute-value cutoff is
proved impossible for it.

The final section proves the corresponding exact Haar coefficient identity.
The complete `A2` same-charge square is the sum of its iterated/iterated
remainder, its full two-orientation mixed interference, and its direct/direct
regular-good square.  No cancellation of the isolated remainder, no RPA
renewal, and no kinetic limit is asserted here.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveMatchedDenominatorForestRank
open ArchonPhysics.CanonicalIIDCoerciveRegularGoodCutoffExponentBalance
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

/-! ## Corrected three-sector structural rank -/

/-- The complete physical `A2/A2` square has exactly three structural sector
types.  `mixed` contains both ordered orientations. -/
inductive CompleteA2StructuralSector where
  | iteratedIterated
  | mixed
  | directDirect
  deriving DecidableEq

/-- Structural classification of an ordered complete-`A2` pair. -/
def completeA2StructuralSector {N : Nat} :
    CompleteSecondPicardCharacterTerm N →
      CompleteSecondPicardCharacterTerm N → CompleteA2StructuralSector
  | Sum.inl _, Sum.inl _ => .iteratedIterated
  | Sum.inl _, Sum.inr _ => .mixed
  | Sum.inr _, Sum.inl _ => .mixed
  | Sum.inr _, Sum.inr _ => .directDirect

/-- Corrected structural loss supplied by the local-phase forest, rather
than by the invalid interaction-pair proxy. -/
def completeA2SectorStructuralLoss : CompleteA2StructuralSector → Nat
  | .iteratedIterated => 3
  | .mixed => 2
  | .directDirect => 1

@[simp] theorem completeA2StructuralSector_inl_inl
    {N : Nat}
    (left right : IteratedQuadraticSecondPicardCharacterTerm N) :
    completeA2StructuralSector (Sum.inl left) (Sum.inl right) =
      .iteratedIterated := rfl

@[simp] theorem completeA2StructuralSector_inl_inr
    {N : Nat}
    (left : IteratedQuadraticSecondPicardCharacterTerm N)
    (right : CubicPhaseTerm N) :
    completeA2StructuralSector (Sum.inl left) (Sum.inr right) = .mixed := rfl

@[simp] theorem completeA2StructuralSector_inr_inl
    {N : Nat} (left : CubicPhaseTerm N)
    (right : IteratedQuadraticSecondPicardCharacterTerm N) :
    completeA2StructuralSector (Sum.inr left) (Sum.inl right) = .mixed := rfl

@[simp] theorem completeA2StructuralSector_inr_inr
    {N : Nat} (left right : CubicPhaseTerm N) :
    completeA2StructuralSector (Sum.inr left) (Sum.inr right) =
      .directDirect := rfl

/-- The sector adapter agrees exactly with the physical local-phase forest
rank, by exhaustive branch classification. -/
theorem physicalCompleteA2MatchedForestRank_eq_sectorStructuralLoss
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (left right : CompleteSecondPicardCharacterTerm N) :
    physicalCompleteA2MatchedForestRank m observed left right =
      completeA2SectorStructuralLoss
        (completeA2StructuralSector left right) := by
  rcases left with left | left <;> rcases right with right | right <;>
    simp [completeA2SectorStructuralLoss, completeA2StructuralSector]

/-- Exactly the mixed and direct/direct sectors have corrected structural
loss at most two. -/
theorem completeA2SectorStructuralLoss_le_two_iff
    (sector : CompleteA2StructuralSector) :
    completeA2SectorStructuralLoss sector ≤ 2 ↔
      sector ≠ .iteratedIterated := by
  cases sector <;> simp [completeA2SectorStructuralLoss]

/-- Pair-level form of the corrected regular-good classification. -/
theorem physicalCompleteA2MatchedForestRank_le_two_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (left right : CompleteSecondPicardCharacterTerm N) :
    physicalCompleteA2MatchedForestRank m observed left right ≤ 2 ↔
      completeA2StructuralSector left right ≠ .iteratedIterated := by
  rw [physicalCompleteA2MatchedForestRank_eq_sectorStructuralLoss,
    completeA2SectorStructuralLoss_le_two_iff]

/-! ## One explicit cutoff for the corrected regular-good sectors -/

/-- A single cutoff exponent works uniformly for both feasible `g^4`
structural ranks. -/
def correctedSecondPicardG4CutoffExponent : Real := 5 / 4

theorem correctedSecondPicardG4CutoffExponent_loss_one :
    CutoffExponentAdmissible 4 1 quadraticKineticDeficit
      correctedSecondPicardG4CutoffExponent := by
  norm_num [CutoffExponentAdmissible, badKineticExponent,
    regularKineticExponent, quadraticKineticDeficit,
    correctedSecondPicardG4CutoffExponent]

theorem correctedSecondPicardG4CutoffExponent_loss_two :
    CutoffExponentAdmissible 4 2 quadraticKineticDeficit
      correctedSecondPicardG4CutoffExponent := by
  norm_num [CutoffExponentAdmissible, badKineticExponent,
    regularKineticExponent, quadraticKineticDeficit,
    correctedSecondPicardG4CutoffExponent]

/-- Closed mixed/direct adapter.  There is no rank hypothesis: the physical
branch classification computes the structural loss before applying the
fixed cutoff. -/
theorem correctedSecondPicardG4CutoffExponent_admissible_of_regularGood
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (left right : CompleteSecondPicardCharacterTerm N)
    (hsector : completeA2StructuralSector left right ≠
      .iteratedIterated) :
    CutoffExponentAdmissible 4
      (physicalCompleteA2MatchedForestRank m observed left right : Real)
      quadraticKineticDeficit correctedSecondPicardG4CutoffExponent := by
  rcases left with left | left <;> rcases right with right | right
  · simp at hsector
  · simpa using correctedSecondPicardG4CutoffExponent_loss_two
  · simpa using correctedSecondPicardG4CutoffExponent_loss_two
  · simpa using correctedSecondPicardG4CutoffExponent_loss_one

/-- Forward mixed ordered pairs close with the uniform explicit cutoff. -/
theorem correctedSecondPicardG4CutoffExponent_admissible_inl_inr
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (left : IteratedQuadraticSecondPicardCharacterTerm N)
    (right : CubicPhaseTerm N) :
    CutoffExponentAdmissible 4
      (physicalCompleteA2MatchedForestRank m observed
        (Sum.inl left) (Sum.inr right) : Real)
      quadraticKineticDeficit correctedSecondPicardG4CutoffExponent := by
  simpa using correctedSecondPicardG4CutoffExponent_loss_two

/-- Reverse mixed ordered pairs close with the same cutoff. -/
theorem correctedSecondPicardG4CutoffExponent_admissible_inr_inl
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (left : CubicPhaseTerm N)
    (right : IteratedQuadraticSecondPicardCharacterTerm N) :
    CutoffExponentAdmissible 4
      (physicalCompleteA2MatchedForestRank m observed
        (Sum.inr left) (Sum.inl right) : Real)
      quadraticKineticDeficit correctedSecondPicardG4CutoffExponent := by
  simpa using correctedSecondPicardG4CutoffExponent_loss_two

/-- Direct/direct ordered pairs close with the same cutoff. -/
theorem correctedSecondPicardG4CutoffExponent_admissible_inr_inr
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (left right : CubicPhaseTerm N) :
    CutoffExponentAdmissible 4
      (physicalCompleteA2MatchedForestRank m observed
        (Sum.inr left) (Sum.inr right) : Real)
      quadraticKineticDeficit correctedSecondPicardG4CutoffExponent := by
  simpa using correctedSecondPicardG4CutoffExponent_loss_one

/-- The isolated iterated/iterated sector cannot be put back into the
absolute-value regular-good estimate by choosing another power cutoff. -/
theorem iteratedIterated_requires_cancellation_or_renormalization
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (left right : IteratedQuadraticSecondPicardCharacterTerm N) :
    ¬ ∃ alpha, CutoffExponentAdmissible 4
      (physicalCompleteA2MatchedForestRank m observed
        (Sum.inl left) (Sum.inl right) : Real)
      quadraticKineticDeficit alpha := by
  exact physicalCompleteA2_inl_inl_no_quadraticCutoffExponent
    m observed left right

/-! ## Exact coefficient-level separation -/

/-- Reversing the two ordered charge families conjugates their selected cross sum. -/
theorem cross_reverse_eq_star
    {d J K : Type*} [Fintype d] [Fintype J] [Fintype K]
    (leftCoefficient : J → Complex) (leftCharge : J → d → Int)
    (rightCoefficient : K → Complex) (rightCharge : K → d → Int) :
    equalChargeCrossPairSum rightCoefficient rightCharge
        leftCoefficient leftCharge =
      starRingEnd Complex
        (equalChargeCrossPairSum leftCoefficient leftCharge
          rightCoefficient rightCharge) := by
  classical
  unfold equalChargeCrossPairSum
  rw [map_sum]
  simp_rw [map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left hleft
  apply Finset.sum_congr rfl
  intro right hright
  by_cases hcharge : leftCharge left = rightCharge right
  · rw [if_pos hcharge.symm, if_pos hcharge]
    simp only [map_mul, starRingEnd_apply, star_star]
    ring
  · have hcharge' : rightCharge right ≠ leftCharge left :=
      fun h ↦ hcharge h.symm
    rw [if_neg hcharge', if_neg hcharge, map_zero]

/-- The selected square on a sum index is the exact sum of its four ordered
branch rectangles. -/
theorem equalChargeCrossPairSum_sum_eq_four
    {d J K : Type*} [Fintype d] [Fintype J] [Fintype K]
    (coefficient : J ⊕ K → Complex) (charge : J ⊕ K → d → Int) :
    equalChargeCrossPairSum coefficient charge coefficient charge =
      equalChargeCrossPairSum
          (fun left : J ↦ coefficient (Sum.inl left))
          (fun left : J ↦ charge (Sum.inl left))
          (fun left : J ↦ coefficient (Sum.inl left))
          (fun left : J ↦ charge (Sum.inl left)) +
        equalChargeCrossPairSum
          (fun left : J ↦ coefficient (Sum.inl left))
          (fun left : J ↦ charge (Sum.inl left))
          (fun right : K ↦ coefficient (Sum.inr right))
          (fun right : K ↦ charge (Sum.inr right)) +
        equalChargeCrossPairSum
          (fun right : K ↦ coefficient (Sum.inr right))
          (fun right : K ↦ charge (Sum.inr right))
          (fun left : J ↦ coefficient (Sum.inl left))
          (fun left : J ↦ charge (Sum.inl left)) +
        equalChargeCrossPairSum
          (fun right : K ↦ coefficient (Sum.inr right))
          (fun right : K ↦ charge (Sum.inr right))
          (fun right : K ↦ coefficient (Sum.inr right))
          (fun right : K ↦ charge (Sum.inr right)) := by
  classical
  unfold equalChargeCrossPairSum
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  simp_rw [Finset.sum_add_distrib]
  ring

/-- A same-charge square indexed by a sum type splits exactly into its two
within-branch squares and the full two-orientation cross interference. -/
theorem sameChargeFamilySquare_sum_eq_branches
    {d J K : Type*} [Fintype d] [Fintype J] [Fintype K]
    (coefficient : J ⊕ K → Complex) (charge : J ⊕ K → d → Int) :
    sameChargeFamilySquare coefficient charge =
      sameChargeFamilySquare
          (fun left : J ↦ coefficient (Sum.inl left))
          (fun left : J ↦ charge (Sum.inl left)) +
        equalChargeFamilyInterference
          (fun left : J ↦ coefficient (Sum.inl left))
          (fun left : J ↦ charge (Sum.inl left))
          (fun right : K ↦ coefficient (Sum.inr right))
          (fun right : K ↦ charge (Sum.inr right)) +
        sameChargeFamilySquare
          (fun right : K ↦ coefficient (Sum.inr right))
          (fun right : K ↦ charge (Sum.inr right)) := by
  rw [sameChargeFamilySquare, equalChargeCrossPairSum_sum_eq_four]
  rw [show equalChargeCrossPairSum
          (fun right : K ↦ coefficient (Sum.inr right))
          (fun right : K ↦ charge (Sum.inr right))
          (fun left : J ↦ coefficient (Sum.inl left))
          (fun left : J ↦ charge (Sum.inl left)) =
        starRingEnd Complex
          (equalChargeCrossPairSum
            (fun left : J ↦ coefficient (Sum.inl left))
            (fun left : J ↦ charge (Sum.inl left))
            (fun right : K ↦ coefficient (Sum.inr right))
            (fun right : K ↦ charge (Sum.inr right))) by
      exact cross_reverse_eq_star _ _ _ _]
  simp only [Complex.add_re, Complex.conj_re]
  unfold sameChargeFamilySquare equalChargeFamilyInterference
  ring

/-- Iterated/iterated part of the complete physical `A2` square.  This is
the cancellation/renormalization remainder singled out by structural rank. -/
def completeA2IteratedIteratedRemainder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) : Real :=
  sameChargeFamilySquare
    (iteratedQuadraticSecondPicardNestedCoefficient
      m kappa radius observed time)
    iteratedQuadraticSecondPicardCharge

/-- Full two-orientation mixed contribution to the complete physical `A2`
square. -/
def completeA2MixedRegularGoodCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) : Real :=
  equalChargeFamilyInterference
    (iteratedQuadraticSecondPicardNestedCoefficient
      m kappa radius observed time)
    iteratedQuadraticSecondPicardCharge
    (oscillatoryCoefficient
      (cubicDuhamelCoefficient
        (physicalCubicUnitCoupling (modeFrequency m observed) beta)
        m observed radius)
      (cubicPhaseMismatch (modeFrequency m) observed) time)
    cubicPhaseCharge

/-- Direct/direct contribution to the complete physical `A2` square. -/
def completeA2DirectRegularGoodCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) : Real :=
  sameChargeFamilySquare
    (oscillatoryCoefficient
      (cubicDuhamelCoefficient
        (physicalCubicUnitCoupling (modeFrequency m observed) beta)
        m observed radius)
      (cubicPhaseMismatch (modeFrequency m) observed) time)
    cubicPhaseCharge

/-- Corrected regular-good `g^4` coefficient: mixed plus direct/direct, with
the rank-three iterated square excluded. -/
def completeA2CorrectedRegularGoodCoefficient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) : Real :=
  completeA2MixedRegularGoodCoefficient
      m kappa beta radius observed time +
    completeA2DirectRegularGoodCoefficient
      m beta radius observed time

/-- Exact corrected decomposition of the complete second-Picard Haar square.
This equality is the adapter consumed by a downstream RPA proof: it may use
the closed mixed/direct cutoff and must estimate the displayed remainder by
cancellation or renormalization. -/
theorem completeSecondPicard_sameChargeFamilySquare_eq_remainder_add_regularGood
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) :
    sameChargeFamilySquare
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge =
      completeA2IteratedIteratedRemainder
          m kappa radius observed time +
        completeA2CorrectedRegularGoodCoefficient
          m kappa beta radius observed time := by
  rw [sameChargeFamilySquare_sum_eq_branches]
  simp only [completeSecondPicardCoefficient_inl,
    completeSecondPicardCoefficient_inr, completeSecondPicardCharge_inl,
    completeSecondPicardCharge_inr]
  unfold completeA2IteratedIteratedRemainder
    completeA2CorrectedRegularGoodCoefficient
    completeA2MixedRegularGoodCoefficient
    completeA2DirectRegularGoodCoefficient
  ring

/-- The exact `g^4` reference term has the same structural separation after
restoring its coupling power. -/
theorem g4_completeSecondPicard_sameChargeFamilySquare_eq_remainder_add_regularGood
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) :
    g ^ 4 * sameChargeFamilySquare
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge =
      g ^ 4 * completeA2IteratedIteratedRemainder
          m kappa radius observed time +
        g ^ 4 * completeA2CorrectedRegularGoodCoefficient
          m kappa beta radius observed time := by
  rw [completeSecondPicard_sameChargeFamilySquare_eq_remainder_add_regularGood]
  ring

end

end ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter
