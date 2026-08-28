import ArchonPhysics.EqualMassPeriodicFPUTFourWaveHaarPhaseCouples

/-!
# Nondegenerate 2-to-2 external-signature classification

An arbitrary equality of four-leg integer signatures need not identify the
individual legs: repeated modes and a positive/negative occurrence at the
same mode can cancel.  This module isolates a transparent nondegenerate
`2 ↔ 2` sector.  Each side has two distinct positive modes, two distinct
negative modes, and no mode occurs with both signs.

In this sector equality of signatures is equivalent to independent
permutations of the two positive legs and the two negative legs.  For actual
effective alpha-FPUT diagrams, a presentation records a literal list
permutation from the four external signed atoms to such a nondegenerate
`2 ↔ 2` list.  Matched Haar couples with presentations therefore reduce to
four possible leg permutations.  Diagrams without a presentation form the
explicit repeated/cancelling/other-sign-sector remainder.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoSignatureClassification

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTFourWaveHaarPhaseCouples
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FinitePhaseMonomialHaarOrthogonality

noncomputable section

/-! ## Abstract nondegenerate two-positive/two-negative data -/

/-- Four signed modes in the nondegenerate `2 ↔ 2` sector. -/
structure NondegenerateTwoToTwoLegs (Mode : Type*) where
  positive : Fin 2 → Mode
  negative : Fin 2 → Mode
  positive_injective : Function.Injective positive
  negative_injective : Function.Injective negative
  positive_ne_negative : ∀ i j, positive i ≠ negative j

/-- Canonical signed list: two positive phase factors followed by two
conjugate factors. -/
def twoToTwoSignedLegList {Mode : Type*}
    (legs : NondegenerateTwoToTwoLegs Mode) : List (SignedMode Mode) :=
  [⟨legs.positive 0, .phase⟩, ⟨legs.positive 1, .phase⟩,
    ⟨legs.negative 0, .conjugate⟩, ⟨legs.negative 1, .conjugate⟩]

/-- Integer external signature of the canonical nondegenerate list. -/
def twoToTwoPhaseSignature {Mode : Type*} [DecidableEq Mode]
    (legs : NondegenerateTwoToTwoLegs Mode) : Mode → Int :=
  phaseSignature (twoToTwoSignedLegList legs)

/-- Explicit signed-indicator formula for the `2 ↔ 2` signature. -/
theorem twoToTwoPhaseSignature_apply
    {Mode : Type*} [DecidableEq Mode]
    (legs : NondegenerateTwoToTwoLegs Mode) (mode : Mode) :
    twoToTwoPhaseSignature legs mode =
      (if mode = legs.positive 0 then 1 else 0) +
      (if mode = legs.positive 1 then 1 else 0) +
      (if mode = legs.negative 0 then -1 else 0) +
      (if mode = legs.negative 1 then -1 else 0) := by
  simp [twoToTwoPhaseSignature, twoToTwoSignedLegList, phaseSignature,
    monomialCharge, SignedMode.charge, PhaseSign.exponent, Pi.single_apply]
  abel

/-- The unordered pair of positive modes. -/
def positiveModeSet {Mode : Type*} [DecidableEq Mode]
    (legs : NondegenerateTwoToTwoLegs Mode) : Finset Mode :=
  {legs.positive 0, legs.positive 1}

/-- The unordered pair of negative modes. -/
def negativeModeSet {Mode : Type*} [DecidableEq Mode]
    (legs : NondegenerateTwoToTwoLegs Mode) : Finset Mode :=
  {legs.negative 0, legs.negative 1}

/-- In the nondegenerate sector, signature value `+1` selects exactly the
positive pair. -/
theorem mem_positiveModeSet_iff_signature_eq_one
    {Mode : Type*} [DecidableEq Mode]
    (legs : NondegenerateTwoToTwoLegs Mode) (mode : Mode) :
    mode ∈ positiveModeSet legs ↔ twoToTwoPhaseSignature legs mode = 1 := by
  have hp : legs.positive 0 ≠ legs.positive 1 :=
    legs.positive_injective.ne (by decide)
  have hm : legs.negative 0 ≠ legs.negative 1 :=
    legs.negative_injective.ne (by decide)
  have h00 := legs.positive_ne_negative 0 0
  have h01 := legs.positive_ne_negative 0 1
  have h10 := legs.positive_ne_negative 1 0
  have h11 := legs.positive_ne_negative 1 1
  rw [twoToTwoPhaseSignature_apply]
  by_cases hp0 : mode = legs.positive 0
  · subst mode
    simp_all [positiveModeSet]
  · by_cases hp1 : mode = legs.positive 1
    · subst mode
      simp_all [positiveModeSet]
    · by_cases hm0 : mode = legs.negative 0
      · subst mode
        simp_all [positiveModeSet]
      · by_cases hm1 : mode = legs.negative 1
        · subst mode
          simp_all [positiveModeSet]
        · simp_all [positiveModeSet]

/-- In the nondegenerate sector, signature value `-1` selects exactly the
negative pair. -/
theorem mem_negativeModeSet_iff_signature_eq_neg_one
    {Mode : Type*} [DecidableEq Mode]
    (legs : NondegenerateTwoToTwoLegs Mode) (mode : Mode) :
    mode ∈ negativeModeSet legs ↔ twoToTwoPhaseSignature legs mode = -1 := by
  have hp : legs.positive 0 ≠ legs.positive 1 :=
    legs.positive_injective.ne (by decide)
  have hm : legs.negative 0 ≠ legs.negative 1 :=
    legs.negative_injective.ne (by decide)
  have h00 := legs.positive_ne_negative 0 0
  have h01 := legs.positive_ne_negative 0 1
  have h10 := legs.positive_ne_negative 1 0
  have h11 := legs.positive_ne_negative 1 1
  rw [twoToTwoPhaseSignature_apply]
  by_cases hp0 : mode = legs.positive 0
  · subst mode
    simp_all [negativeModeSet]
  · by_cases hp1 : mode = legs.positive 1
    · subst mode
      simp_all [negativeModeSet]
    · by_cases hm0 : mode = legs.negative 0
      · subst mode
        simp_all [negativeModeSet]
      · by_cases hm1 : mode = legs.negative 1
        · subst mode
          simp_all [negativeModeSet]
        · simp_all [negativeModeSet]

/-- Equality of two-element finsets with a distinct left pair gives the two
possible pair permutations. -/
theorem pairSet_eq_pairSet_classification
    {Mode : Type*} [DecidableEq Mode]
    {a b c d : Mode} (hab : a ≠ b)
    (hset : ({a, b} : Finset Mode) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha_mem : a ∈ ({c, d} : Finset Mode) := by
    rw [← hset]
    simp
  have hb_mem : b ∈ ({c, d} : Finset Mode) := by
    rw [← hset]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem hb_mem
  rcases ha_mem with hac | had
  · left
    refine ⟨hac, ?_⟩
    rcases hb_mem with hbc | hbd
    · exact False.elim (hab (hac.trans hbc.symm))
    · exact hbd
  · right
    refine ⟨had, ?_⟩
    rcases hb_mem with hbc | hbd
    · exact hbc
    · exact False.elim (hab (had.trans hbd.symm))

/-- Independent permutations of the positive pair and negative pair. -/
def IsTwoToTwoLegPermutation {Mode : Type*}
    (left right : NondegenerateTwoToTwoLegs Mode) : Prop :=
  ((left.positive 0 = right.positive 0 ∧
      left.positive 1 = right.positive 1) ∨
    (left.positive 0 = right.positive 1 ∧
      left.positive 1 = right.positive 0)) ∧
  ((left.negative 0 = right.negative 0 ∧
      left.negative 1 = right.negative 1) ∨
    (left.negative 0 = right.negative 1 ∧
      left.negative 1 = right.negative 0))

/-- Signature equality forces independent permutations of positive and
negative legs. -/
theorem twoToTwoPhaseSignature_eq_implies_legPermutation
    {Mode : Type*} [DecidableEq Mode]
    (left right : NondegenerateTwoToTwoLegs Mode)
    (hsignature : twoToTwoPhaseSignature left =
      twoToTwoPhaseSignature right) :
    IsTwoToTwoLegPermutation left right := by
  have hpositiveSet : positiveModeSet left = positiveModeSet right := by
    ext mode
    rw [mem_positiveModeSet_iff_signature_eq_one,
      mem_positiveModeSet_iff_signature_eq_one, hsignature]
  have hnegativeSet : negativeModeSet left = negativeModeSet right := by
    ext mode
    rw [mem_negativeModeSet_iff_signature_eq_neg_one,
      mem_negativeModeSet_iff_signature_eq_neg_one, hsignature]
  constructor
  · exact pairSet_eq_pairSet_classification
      (left.positive_injective.ne (by decide)) hpositiveSet
  · exact pairSet_eq_pairSet_classification
      (left.negative_injective.ne (by decide)) hnegativeSet

/-- Conversely, separate positive/negative pair permutations preserve the
integer signature. -/
theorem twoToTwoPhaseSignature_eq_of_legPermutation
    {Mode : Type*} [DecidableEq Mode]
    (left right : NondegenerateTwoToTwoLegs Mode)
    (hperm : IsTwoToTwoLegPermutation left right) :
    twoToTwoPhaseSignature left = twoToTwoPhaseSignature right := by
  funext mode
  rw [twoToTwoPhaseSignature_apply, twoToTwoPhaseSignature_apply]
  rcases hperm with ⟨(hp | hp), (hm | hm)⟩
  all_goals rcases hp with ⟨hp0, hp1⟩
  all_goals rcases hm with ⟨hm0, hm1⟩
  all_goals simp only [hp0, hp1, hm0, hm1]
  all_goals ring

/-- Complete nondegenerate `2 ↔ 2` classification. -/
theorem twoToTwoPhaseSignature_eq_iff_legPermutation
    {Mode : Type*} [DecidableEq Mode]
    (left right : NondegenerateTwoToTwoLegs Mode) :
    twoToTwoPhaseSignature left = twoToTwoPhaseSignature right ↔
      IsTwoToTwoLegPermutation left right := by
  constructor
  · exact twoToTwoPhaseSignature_eq_implies_legPermutation left right
  · exact twoToTwoPhaseSignature_eq_of_legPermutation left right

/-! ## Actual effective-diagram adapter -/

/-- Monomial signatures are invariant under a literal permutation of signed
factors. -/
theorem phaseSignature_eq_of_list_perm
    {Mode : Type*} [DecidableEq Mode]
    {left right : List (SignedMode Mode)} (hperm : left.Perm right) :
    phaseSignature left = phaseSignature right := by
  funext mode
  rw [phaseSignature, phaseSignature,
    monomialCharge_apply, monomialCharge_apply]
  exact (hperm.map fun factor ↦
    if mode = factor.mode then factor.sign.exponent else 0).sum_eq

/-- A transparent certificate that an actual effective diagram lies in the
nondegenerate `2 ↔ 2` sector.  The permutation field concerns the literal
four `(mode, sign)` atoms, not merely their already-summed signature. -/
structure ExternalTwoToTwoPresentation
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) where
  legs : NondegenerateTwoToTwoLegs (Lattice.Site N)
  atom_perm : (externalFourWaveMonomial diagram).Perm
    (twoToTwoSignedLegList legs)

/-- Membership in the classified nondegenerate `2 ↔ 2` sector. -/
def HasNondegenerateTwoToTwoPresentation
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Prop :=
  Nonempty (ExternalTwoToTwoPresentation diagram)

/-- Transparent remainder left outside the permutation classification.  It
contains repeated legs, positive/negative cancellation at one mode, and all
external sign sectors other than presented nondegenerate `2 ↔ 2`. -/
def IsTwoToTwoClassificationRemainder
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Prop :=
  ¬ HasNondegenerateTwoToTwoPresentation diagram

/-- Every diagram is explicitly routed either to the classified sector or
to the transparent remainder. -/
theorem nondegenerateTwoToTwo_or_classificationRemainder
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    HasNondegenerateTwoToTwoPresentation diagram ∨
      IsTwoToTwoClassificationRemainder diagram := by
  exact Classical.em _

/-- A presentation identifies the actual external signature with its
canonical nondegenerate `2 ↔ 2` signature. -/
theorem ExternalTwoToTwoPresentation.signature_eq
    {N : Nat} [NeZero N] {diagram : EffectiveFourWaveDiagram N}
    (presentation : ExternalTwoToTwoPresentation diagram) :
    externalFourWavePhaseSignature diagram =
      twoToTwoPhaseSignature presentation.legs := by
  exact phaseSignature_eq_of_list_perm presentation.atom_perm

/-- For two presented actual diagrams, Haar matching is equivalent to the
four independent choices generated by swapping the positive pair and/or the
negative pair. -/
theorem externalFourWavePhaseSignature_eq_iff_twoToTwoLegPermutation
    {N : Nat} [NeZero N]
    {left right : EffectiveFourWaveDiagram N}
    (leftPresentation : ExternalTwoToTwoPresentation left)
    (rightPresentation : ExternalTwoToTwoPresentation right) :
    externalFourWavePhaseSignature left =
        externalFourWavePhaseSignature right ↔
      IsTwoToTwoLegPermutation leftPresentation.legs
        rightPresentation.legs := by
  rw [leftPresentation.signature_eq, rightPresentation.signature_eq]
  exact twoToTwoPhaseSignature_eq_iff_legPermutation
    leftPresentation.legs rightPresentation.legs

/-- Presented matched binary-tree couples reduce to the same four leg
permutations. -/
theorem leafPhaseBalanced_iff_twoToTwoLegPermutation
    {N : Nat} [NeZero N]
    {left right : EffectiveFourWaveDiagram N}
    (leftPresentation : ExternalTwoToTwoPresentation left)
    (rightPresentation : ExternalTwoToTwoPresentation right) :
    PhyslibFPUTBinaryInteractionTreeCouples.leafPhaseBalanced
        (externalFourWaveDiagramCouple left right) ↔
      IsTwoToTwoLegPermutation leftPresentation.legs
        rightPresentation.legs := by
  rw [leafPhaseBalanced_externalFourWaveDiagramCouple_iff]
  exact externalFourWavePhaseSignature_eq_iff_twoToTwoLegPermutation
    leftPresentation rightPresentation

/-- Matched-couple remainder: the pair is Haar matched, but at least one
diagram lies outside the presented nondegenerate `2 ↔ 2` sector. -/
def IsMatchedTwoToTwoClassificationRemainder
    {N : Nat} [NeZero N]
    (left right : EffectiveFourWaveDiagram N) : Prop :=
  PhyslibFPUTBinaryInteractionTreeCouples.leafPhaseBalanced
      (externalFourWaveDiagramCouple left right) ∧
    (IsTwoToTwoClassificationRemainder left ∨
      IsTwoToTwoClassificationRemainder right)

/-- Every Haar-matched diagram pair is either one of the four classified
positive/negative pair permutations, with explicit presentations, or belongs
to the transparent matched remainder. -/
theorem matchedCouple_classifiedPermutation_or_remainder
    {N : Nat} [NeZero N]
    (left right : EffectiveFourWaveDiagram N)
    (hmatched : PhyslibFPUTBinaryInteractionTreeCouples.leafPhaseBalanced
      (externalFourWaveDiagramCouple left right)) :
    (∃ (leftPresentation : ExternalTwoToTwoPresentation left)
        (rightPresentation : ExternalTwoToTwoPresentation right),
      IsTwoToTwoLegPermutation leftPresentation.legs
        rightPresentation.legs) ∨
      IsMatchedTwoToTwoClassificationRemainder left right := by
  by_cases hleft : HasNondegenerateTwoToTwoPresentation left
  · by_cases hright : HasNondegenerateTwoToTwoPresentation right
    · rcases hleft with ⟨leftPresentation⟩
      rcases hright with ⟨rightPresentation⟩
      left
      exact ⟨leftPresentation, rightPresentation,
        (leafPhaseBalanced_iff_twoToTwoLegPermutation
          leftPresentation rightPresentation).1 hmatched⟩
    · right
      exact ⟨hmatched, Or.inr hright⟩
  · right
    exact ⟨hmatched, Or.inl hleft⟩

end

end ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoSignatureClassification
