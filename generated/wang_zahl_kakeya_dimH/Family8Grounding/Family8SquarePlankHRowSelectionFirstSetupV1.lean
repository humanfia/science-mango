import Family8Grounding.Family8HRowSourceAverageRetentionFromOwnerSelectionV1
import Family8Grounding.Family8PlankHeavyRetainedOwnerActualDatumV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SquarePlankHRowSelectionFirstSetupV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.CubeWeightUniformization
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8HRowSourceAverageRetentionFromOwnerSelectionV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActualDatumV2
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a : NNReal}

/-- The single selected cell retains the complete graph source. -/
def universalHRowCell (_ : Unit) : Set Space := Set.univ

theorem universalHRowCell_measurable (p : Unit) :
    MeasurableSet (universalHRowCell p) := by
  simp [universalHRowCell]

@[simp] theorem restrictToUniversalHRowCell_carrier
    {F : ConvexFamily iota} (Y : Shading F) (i : iota) :
    (restrictToCells Y universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit)).carrier i = Y.carrier i := by
  have hregion : selectedRegion universalHRowCell
      (Finset.univ : Finset Unit) = Set.univ := by
    ext x
    constructor
    · exact fun _ => Set.mem_univ x
    · intro _hx
      exact Set.mem_iUnion.mpr ⟨(), Set.mem_iUnion.mpr
        ⟨Finset.mem_univ (), Set.mem_univ x⟩⟩
  rw [restrictToCells_carrier, hregion, Set.inter_univ]

/-- At aspect ratio one, source cardinality is an honest thick-control
constant. -/
theorem squarePlank_fintypeCard_frostmanThickenedPlankControl
    [Nonempty iota]
    (D : ShadedConvexPlankFamily iota a a) (ha : 0 < a) :
    FrostmanThickenedPlankControl D (Fintype.card iota : NNReal) := by
  constructor
  · exact_mod_cast (Fintype.card_pos : 0 < Fintype.card iota)
  · intro theta hatheta htheta i
    have ha0 : a ≠ 0 := ne_of_gt ha
    have honeLe : (1 : NNReal) ≤ theta := by
      simpa only [div_self ha0] using hatheta
    have hthetaOne : theta = 1 := le_antisymm htheta honeLe
    subst theta
    simpa using
      (show ((thickenedPlankIndices D 1 i).card : ENNReal) ≤
          (Fintype.card iota : ENNReal) by
        exact_mod_cast Finset.card_le_univ
          (s := thickenedPlankIndices D 1 i))

/-- Minimal finite selection data before any fresh analytic budget. -/
structure SquarePlankHRowSelectionFirstSetup
    (D : ShadedConvexPlankFamily iota a a) where
  C : MutualThickeningClustering D 1
  q : Fin (Nat.log 2 (Fintype.card iota) + 1)
  retained_mass_ne_zero :
    (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0
  active_nonempty :
    (activeRetainedOwnerCellIndices D C q universalHRowCell
      universalHRowCell_measurable (Finset.univ : Finset Unit)).Nonempty
  source_mass_retained :
    D.shading.shadingMass ≤
      (Nat.log 2 (Fintype.card iota) + 1 : Nat) *
        (retainedOwnerPlankFamily D C q).shading.shadingMass

def SquarePlankHRowSelectionFirstSetup.loss
    {D : ShadedConvexPlankFamily iota a a}
    (R : SquarePlankHRowSelectionFirstSetup D) : ENNReal :=
  (Nat.log 2 (Fintype.card iota) + 1 : Nat) *
    ownerBucketToHRowLoss R.C R.q

/-- Construct clustering, owner bucket, and nonempty unrestricted cell
support from a nonzero square-plank source. -/
theorem exists_squarePlankHRowSelectionFirstSetup
    [Nonempty iota]
    (D : ShadedConvexPlankFamily iota a a) (ha : 0 < a)
    (hsourceMass : D.shading.shadingMass ≠ 0) :
    Nonempty (SquarePlankHRowSelectionFirstSetup D) := by
  let M : NNReal := Fintype.card iota
  have hthick : FrostmanThickenedPlankControl D M := by
    simpa only [M] using
      squarePlank_fintypeCard_frostmanThickenedPlankControl D ha
  let C : MutualThickeningClustering D 1 :=
    Classical.choice (exists_mutualThickeningClustering D 1)
  obtain ⟨q, hretained, _hbranch, _hbounds⟩ :=
    exists_retainedOwnerPlankFamily_mass_card_thickControl
      D M 1 C hthick (by simp [ne_of_gt ha]) le_rfl
  have hretained0 :
      (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0 := by
    intro hzero
    apply hsourceMass
    apply le_antisymm
    · simpa only [hzero, mul_zero] using hretained
    · exact bot_le
  have hheavy0 :
      (heavyRetainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0 := by
    intro hzero
    apply hretained0
    apply le_antisymm
    · simpa only [hzero, mul_zero] using
        (retainedOwnerPlankFamily_mass_le_two_mul_heavyActualMass D C q)
    · exact bot_le
  have hactive :
      (activeRetainedOwnerCellIndices D C q universalHRowCell
        universalHRowCell_measurable (Finset.univ : Finset Unit)).Nonempty := by
    by_contra hempty
    have hallEmpty : ∀ i : {i // i ∈ heavyRetainedOwnerSourceIndices C q},
        (heavyRetainedOwnerPlankFamily D C q).shading.carrier i = ∅ := by
      intro i
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hi
      apply hempty
      refine ⟨i, (mem_activeRetainedOwnerCellIndices
        D C q universalHRowCell universalHRowCell_measurable
          (Finset.univ : Finset Unit) i).2 ?_⟩
      simpa only [heavyRetainedOwnerFinalFineShading,
        restrictToUniversalHRowCell_carrier] using hi
    apply hheavy0
    unfold Shading.shadingMass
    apply Finset.sum_eq_zero
    intro i _hi
    rw [hallEmpty i]
    simp
  exact Nonempty.intro
    { C := C
      q := q
      retained_mass_ne_zero := hretained0
      active_nonempty := hactive
      source_mass_retained := hretained }

/-- Every bundle subsequently produced on this exact setup is correlated
with the original source average. -/
theorem SquarePlankHRowSelectionFirstSetup.sourceAverage_le_loss_mul_hRowAverage
    {D : ShadedConvexPlankFamily iota a a}
    (R : SquarePlankHRowSelectionFirstSetup D)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D R.C R.q universalHRowCell universalHRowCell_measurable
        (Finset.univ : Finset Unit) R.retained_mass_ne_zero
          R.active_nonempty epsilon beta eta) :
    D.shading.averageMultiplicity ≤ R.loss *
      (HRowFreshPlankDatum
        D R.C R.q universalHRowCell universalHRowCell_measurable
          (Finset.univ : Finset Unit) R.retained_mass_ne_zero
            R.active_nonempty B.tau B.S).shading.averageMultiplicity := by
  simpa only [SquarePlankHRowSelectionFirstSetup.loss] using
    sourceAverage_le_ownerSelectionLoss_mul_hRowAverage
      D R.C R.q universalHRowCell universalHRowCell_measurable
        (Finset.univ : Finset Unit) R.retained_mass_ne_zero
          R.active_nonempty B
          (Nat.log 2 (Fintype.card iota) + 1 : Nat)
            R.source_mass_retained

#print axioms restrictToUniversalHRowCell_carrier
#print axioms squarePlank_fintypeCard_frostmanThickenedPlankControl
#print axioms exists_squarePlankHRowSelectionFirstSetup
#print axioms
  SquarePlankHRowSelectionFirstSetup.sourceAverage_le_loss_mul_hRowAverage

end
end Family8SquarePlankHRowSelectionFirstSetupV1
