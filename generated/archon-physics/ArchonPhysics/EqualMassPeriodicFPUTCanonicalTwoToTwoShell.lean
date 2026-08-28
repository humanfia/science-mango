import ArchonPhysics.EqualMassPeriodicFPUTFourWaveRemainderCounting

/-!
# Canonical rooted two-to-two shell for effective four-wave diagrams

The output leg of an effective diagram is always positive.  In the actual
`2 ↔ 2` sign sector, exactly one of the spectator and two inner leaves is
positive.  This gives a canonical permutation which keeps the output first,
puts the other positive leg second, and puts the two negative legs last.

For a momentum-supported diagram the resulting ordered external modes lie on
the reduced fixed-output shell.  Degeneracy of the literal four external
modes is therefore exactly the four-graph-line predicate from
`EqualMassPeriodicFPUTFourWaveRemainderCounting`.

There is an important type-level distinction.  The older
`ExternalTwoToTwoPresentation` already requires all four underlying modes to
be distinct, so a "presented-degenerate" diagram in that older sense is
empty.  The counting theorem below consequently uses the wider, explicit
actual sign-sector predicate rather than silently weakening that structure.
It proves the complete fixed-output degenerate actual family has cardinal at
most `128 * N`, compared with the ambient `32 * N^2` bound.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTFourWaveHaarPhaseCouples
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoSignatureClassification
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.EqualMassPeriodicFPUTFourWaveRemainderCounting
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.Lattice

noncomputable section

/-! ## The actual two-to-two sign sector and its canonical slot permutation -/

/-- With the output sign fixed to `plus`, these are the three and only three
literal `2 ↔ 2` sign patterns. -/
def IsExternalTwoToTwoSignSector
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Prop :=
  (totalFourWaveSign diagram 1 = .plus ∧
      totalFourWaveSign diagram 2 = .minus ∧
      totalFourWaveSign diagram 3 = .minus) ∨
    (totalFourWaveSign diagram 1 = .minus ∧
      totalFourWaveSign diagram 2 = .plus ∧
      totalFourWaveSign diagram 3 = .minus) ∨
    (totalFourWaveSign diagram 1 = .minus ∧
      totalFourWaveSign diagram 2 = .minus ∧
      totalFourWaveSign diagram 3 = .plus)

/-- Slot permutation for the pattern with an inner-left positive leg. -/
def innerLeftPositiveSlotEquiv : Fin 4 ≃ Fin 4 where
  toFun := ![0, 2, 1, 3]
  invFun := ![0, 2, 1, 3]
  left_inv slot := by fin_cases slot <;> rfl
  right_inv slot := by fin_cases slot <;> rfl

/-- Slot permutation for the pattern with an inner-right positive leg. -/
def innerRightPositiveSlotEquiv : Fin 4 ≃ Fin 4 where
  toFun := ![0, 3, 1, 2]
  invFun := ![0, 2, 3, 1]
  left_inv slot := by fin_cases slot <;> rfl
  right_inv slot := by fin_cases slot <;> rfl

/-- Canonical rooted slot ordering.  It is deterministic and depends only on
the actual diagram signs, not on a chosen presentation proof. -/
def canonicalTwoToTwoSlotEquiv
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Fin 4 ≃ Fin 4 :=
  if totalFourWaveSign diagram 1 = .plus then Equiv.refl (Fin 4)
  else if totalFourWaveSign diagram 2 = .plus then
    innerLeftPositiveSlotEquiv
  else innerRightPositiveSlotEquiv

/-- Actual external modes in canonical `output, other-plus, minus, minus`
order. -/
def canonicalTwoToTwoExternalModes
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Fin 4 → Site N :=
  fun slot ↦ totalFourWaveModes diagram
    (canonicalTwoToTwoSlotEquiv diagram slot)

/-- The two free reduced-shell modes: other positive, then first negative. -/
def canonicalTwoToTwoFreePair
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) : Site N × Site N :=
  (canonicalTwoToTwoExternalModes diagram 1,
    canonicalTwoToTwoExternalModes diagram 2)

/-- Canonical signed list associated with the rooted slot ordering. -/
def canonicalTwoToTwoSignedLegList
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    List (SignedMode (Site N)) :=
  [⟨canonicalTwoToTwoExternalModes diagram 0, .phase⟩,
    ⟨canonicalTwoToTwoExternalModes diagram 1, .phase⟩,
    ⟨canonicalTwoToTwoExternalModes diagram 2, .conjugate⟩,
    ⟨canonicalTwoToTwoExternalModes diagram 3, .conjugate⟩]

@[simp] theorem canonicalTwoToTwoExternalModes_zero
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    canonicalTwoToTwoExternalModes diagram 0 = outputMomentum diagram := by
  unfold canonicalTwoToTwoExternalModes canonicalTwoToTwoSlotEquiv
  split_ifs <;> rfl

theorem injective_canonicalTwoToTwoExternalModes_iff
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    Function.Injective (canonicalTwoToTwoExternalModes diagram) ↔
      Function.Injective (totalFourWaveModes diagram) := by
  constructor
  · intro hcanonical left right heq
    let equivalence := canonicalTwoToTwoSlotEquiv diagram
    have hinverse := hcanonical
      (a₁ := equivalence.symm left) (a₂ := equivalence.symm right)
      (by simpa [canonicalTwoToTwoExternalModes, equivalence] using heq)
    simpa [equivalence] using congrArg equivalence hinverse
  · intro hactual left right heq
    apply (canonicalTwoToTwoSlotEquiv diagram).injective
    apply hactual
    exact heq

/-- In the actual `2 ↔ 2` sector, canonical rooting is a literal
permutation of the four signed external atoms. -/
theorem externalFourWaveMonomial_perm_canonicalTwoToTwoSignedLegList
    {N : Nat} (diagram : EffectiveFourWaveDiagram N)
    (hsector : IsExternalTwoToTwoSignSector diagram) :
    (externalFourWaveMonomial diagram).Perm
      (canonicalTwoToTwoSignedLegList diagram) := by
  rcases hsector with hsector | hsector | hsector
  all_goals rcases hsector with ⟨hslotOne, hslotTwo, hslotThree⟩
  · simp [externalFourWaveMonomial, externalFourWaveFactor,
      canonicalTwoToTwoSignedLegList, canonicalTwoToTwoExternalModes,
      canonicalTwoToTwoSlotEquiv, hslotOne, hslotTwo, hslotThree,
      interactionSignToPhaseSign]
  · have hperm :
        ([externalFourWaveFactor diagram 0,
            externalFourWaveFactor diagram 1,
            externalFourWaveFactor diagram 2,
            externalFourWaveFactor diagram 3] :
          List (SignedMode (Site N))).Perm
        [externalFourWaveFactor diagram 0,
          externalFourWaveFactor diagram 2,
          externalFourWaveFactor diagram 1,
          externalFourWaveFactor diagram 3] :=
      List.Perm.cons _ (List.Perm.swap _ _ [_]).symm
    simpa [externalFourWaveMonomial, externalFourWaveFactor,
      canonicalTwoToTwoSignedLegList, canonicalTwoToTwoExternalModes,
      canonicalTwoToTwoSlotEquiv, hslotOne, hslotTwo, hslotThree,
      innerLeftPositiveSlotEquiv, interactionSignToPhaseSign] using hperm
  · have hperm :
        ([externalFourWaveFactor diagram 0,
            externalFourWaveFactor diagram 1,
            externalFourWaveFactor diagram 2,
            externalFourWaveFactor diagram 3] :
          List (SignedMode (Site N))).Perm
        [externalFourWaveFactor diagram 0,
          externalFourWaveFactor diagram 3,
          externalFourWaveFactor diagram 1,
          externalFourWaveFactor diagram 2] :=
      List.Perm.cons _
        ((List.Perm.cons _ (List.Perm.swap _ _ []).symm).trans
          (List.Perm.swap _ _ [_]).symm)
    simpa [externalFourWaveMonomial, externalFourWaveFactor,
      canonicalTwoToTwoSignedLegList, canonicalTwoToTwoExternalModes,
      canonicalTwoToTwoSlotEquiv, hslotOne, hslotTwo, hslotThree,
      innerRightPositiveSlotEquiv, interactionSignToPhaseSign] using hperm

/-! ## Momentum shell and exact degeneracy adapter -/

/-- Supported canonical ordering satisfies the literal `(+,+,-,-)` shell
equation. -/
theorem output_add_canonicalOtherPositive_eq_negatives
    {N : Nat} (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hsector : IsExternalTwoToTwoSignSector diagram) :
    outputMomentum diagram + canonicalTwoToTwoExternalModes diagram 1 =
      canonicalTwoToTwoExternalModes diagram 2 +
        canonicalTwoToTwoExternalModes diagram 3 := by
  have hmomentum :=
    totalFourWaveMomentum_eq_zero_of_supported diagram hsupported
  unfold totalFourWaveMomentum signedFourierMomentum at hmomentum
  rw [Fin.sum_univ_four] at hmomentum
  rcases hsector with hsector | hsector | hsector
  all_goals
    rcases hsector with ⟨hslotOne, hslotTwo, hslotThree⟩
    simp only [totalFourWaveSign_zero, totalFourWaveModes_zero,
      totalFourWaveModes_one, totalFourWaveModes_two,
      totalFourWaveModes_three, hslotOne, hslotTwo, hslotThree,
      interactionSignMomentum] at hmomentum
    simp [canonicalTwoToTwoExternalModes,
      canonicalTwoToTwoSlotEquiv, hslotOne, hslotTwo,
      innerLeftPositiveSlotEquiv, innerRightPositiveSlotEquiv,
      totalFourWaveModes_one,
      totalFourWaveModes_two, totalFourWaveModes_three]
    linear_combination hmomentum

/-- The fourth reduced-shell mode is exactly the second canonically ordered
negative external mode. -/
theorem reducedFourth_eq_canonicalSecondNegative
    {N : Nat} (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hsector : IsExternalTwoToTwoSignSector diagram) :
    outputMomentum diagram + (canonicalTwoToTwoFreePair diagram).1 -
        (canonicalTwoToTwoFreePair diagram).2 =
      canonicalTwoToTwoExternalModes diagram 3 := by
  unfold canonicalTwoToTwoFreePair
  rw [output_add_canonicalOtherPositive_eq_negatives diagram hsupported hsector]
  abel

/-- The reduced-shell four-vector is the canonically permuted actual
external-mode vector. -/
theorem reducedTwoToTwoExternalModes_eq_canonical
    {N : Nat} (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hsector : IsExternalTwoToTwoSignSector diagram) :
    reducedTwoToTwoExternalModes (outputMomentum diagram)
        (canonicalTwoToTwoFreePair diagram) =
      canonicalTwoToTwoExternalModes diagram := by
  funext slot
  fin_cases slot
  · simp [reducedTwoToTwoExternalModes]
  · rfl
  · rfl
  · exact reducedFourth_eq_canonicalSecondNegative diagram
      hsupported hsector

/-- Literal external-mode degeneracy is exactly membership in the four
reduced graph lines, after canonical rooting at the output mode. -/
theorem externalModes_not_injective_iff_canonicalFreePair_degenerate
    {N : Nat} [NeZero N] (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hsector : IsExternalTwoToTwoSignSector diagram) :
    ¬ Function.Injective (totalFourWaveModes diagram) ↔
      IsDegenerateTwoToTwoFreePair (outputMomentum diagram)
        (canonicalTwoToTwoFreePair diagram) := by
  rw [← not_injective_reducedTwoToTwoExternalModes_iff]
  rw [reducedTwoToTwoExternalModes_eq_canonical diagram hsupported hsector]
  exact not_congr (injective_canonicalTwoToTwoExternalModes_iff diagram).symm

/-- The actual canonical fixed-output shell.  Its definition uses the two
free modes; the preceding theorem proves that its completed fourth mode is
the actual remaining negative leg. -/
def canonicalTwoToTwoMomentumShell
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    TwoToTwoMomentumShell N (outputMomentum diagram) :=
  twoToTwoShellFromFree (outputMomentum diagram)
    (canonicalTwoToTwoFreePair diagram)

@[simp] theorem shellModeOne_canonicalTwoToTwoMomentumShell
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    shellModeOne (canonicalTwoToTwoMomentumShell diagram) =
      canonicalTwoToTwoExternalModes diagram 1 := rfl

@[simp] theorem shellModeTwo_canonicalTwoToTwoMomentumShell
    {N : Nat} (diagram : EffectiveFourWaveDiagram N) :
    shellModeTwo (canonicalTwoToTwoMomentumShell diagram) =
      canonicalTwoToTwoExternalModes diagram 2 := rfl

theorem shellModeThree_canonicalTwoToTwoMomentumShell
    {N : Nat} (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hsector : IsExternalTwoToTwoSignSector diagram) :
    shellModeThree (canonicalTwoToTwoMomentumShell diagram) =
      canonicalTwoToTwoExternalModes diagram 3 :=
  reducedFourth_eq_canonicalSecondNegative diagram hsupported hsector

/-! ## Adapter from the older nondegenerate presentation -/

/-- A nondegenerate presentation explicitly forces one of the three actual
`2 ↔ 2` sign patterns.  Existence is consumed as data; it is not assumed
globally. -/
theorem externalTwoToTwoPresentation_isExternalTwoToTwoSignSector
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (presentation : ExternalTwoToTwoPresentation diagram) :
    IsExternalTwoToTwoSignSector diagram := by
  have hsignPerm := presentation.atom_perm.map
    (fun factor : SignedMode (Site N) ↦ factor.sign)
  have hcount := hsignPerm.count_eq PhaseSign.phase
  cases hslotOne : totalFourWaveSign diagram 1 <;>
    cases hslotTwo : totalFourWaveSign diagram 2 <;>
    cases hslotThree : totalFourWaveSign diagram 3 <;>
    simp [IsExternalTwoToTwoSignSector, externalFourWaveMonomial,
      externalFourWaveFactor,
      twoToTwoSignedLegList, hslotOne, hslotTwo, hslotThree,
      interactionSignToPhaseSign] at hcount ⊢

/-- The word "nondegenerate" in the older presentation is substantive: a
diagram carrying such a presentation cannot belong to the external-mode
degeneracy remainder. -/
theorem externalTwoToTwoPresentation_externalModes_injective
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (presentation : ExternalTwoToTwoPresentation diagram) :
    Function.Injective (totalFourWaveModes diagram) := by
  have hmodePerm := presentation.atom_perm.map
    (fun factor : SignedMode (Site N) ↦ factor.mode)
  have hpositive : presentation.legs.positive 0 ≠
      presentation.legs.positive 1 :=
    presentation.legs.positive_injective.ne (by decide)
  have hnegative : presentation.legs.negative 0 ≠
      presentation.legs.negative 1 :=
    presentation.legs.negative_injective.ne (by decide)
  have htarget :
      ((twoToTwoSignedLegList presentation.legs).map
        (fun factor : SignedMode (Site N) ↦ factor.mode)).Nodup := by
    simp [twoToTwoSignedLegList, hpositive, hnegative,
      presentation.legs.positive_ne_negative]
  have hsource :
      ((externalFourWaveMonomial diagram).map
        (fun factor : SignedMode (Site N) ↦ factor.mode)).Nodup :=
    (hmodePerm.nodup_iff).2 htarget
  simp [externalFourWaveMonomial, externalFourWaveFactor] at hsource
  intro left right heq
  fin_cases left <;> fin_cases right <;> simp_all

/-- Consequently there are no diagrams which are simultaneously presented
in the older sense and externally degenerate. -/
theorem not_externalModes_degenerate_of_presentation
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (presentation : ExternalTwoToTwoPresentation diagram) :
    ¬ (¬ Function.Injective (totalFourWaveModes diagram)) :=
  not_not.mpr
    (externalTwoToTwoPresentation_externalModes_injective presentation)

/-- Canonical rooted legs, now equipped with the nondegeneracy proof supplied
by an older presentation. -/
def canonicalNondegenerateTwoToTwoLegs
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (presentation : ExternalTwoToTwoPresentation diagram) :
    NondegenerateTwoToTwoLegs (Site N) := by
  have hinjective :
      Function.Injective (canonicalTwoToTwoExternalModes diagram) :=
    (injective_canonicalTwoToTwoExternalModes_iff diagram).2
      (externalTwoToTwoPresentation_externalModes_injective presentation)
  exact
    { positive := ![canonicalTwoToTwoExternalModes diagram 0,
        canonicalTwoToTwoExternalModes diagram 1]
      negative := ![canonicalTwoToTwoExternalModes diagram 2,
        canonicalTwoToTwoExternalModes diagram 3]
      positive_injective := by
        intro left right heq
        fin_cases left <;> fin_cases right
        · rfl
        · exact False.elim ((hinjective.ne (by decide :
            (0 : Fin 4) ≠ 1)) (by simpa using heq))
        · exact False.elim ((hinjective.ne (by decide :
            (1 : Fin 4) ≠ 0)) (by simpa using heq))
        · rfl
      negative_injective := by
        intro left right heq
        fin_cases left <;> fin_cases right
        · rfl
        · exact False.elim ((hinjective.ne (by decide :
            (2 : Fin 4) ≠ 3)) heq)
        · exact False.elim ((hinjective.ne (by decide :
            (3 : Fin 4) ≠ 2)) heq)
        · rfl
      positive_ne_negative := by
        intro positiveSlot negativeSlot
        fin_cases positiveSlot <;> fin_cases negativeSlot
        · exact hinjective.ne (by decide : (0 : Fin 4) ≠ 2)
        · exact hinjective.ne (by decide : (0 : Fin 4) ≠ 3)
        · exact hinjective.ne (by decide : (1 : Fin 4) ≠ 2)
        · exact hinjective.ne (by decide : (1 : Fin 4) ≠ 3) }

/-- Relative to the canonical rooted legs, any older presentation is one of
the four independent swaps of the positive and negative pairs. -/
theorem canonicalNondegenerateTwoToTwoLegs_isLegPermutation
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (presentation : ExternalTwoToTwoPresentation diagram) :
    IsTwoToTwoLegPermutation
      (canonicalNondegenerateTwoToTwoLegs presentation)
      presentation.legs := by
  apply twoToTwoPhaseSignature_eq_implies_legPermutation
  apply phaseSignature_eq_of_list_perm
  have hcanonical :=
    (externalFourWaveMonomial_perm_canonicalTwoToTwoSignedLegList diagram
      (externalTwoToTwoPresentation_isExternalTwoToTwoSignSector
        presentation)).symm
  have hperm := hcanonical.trans presentation.atom_perm
  simpa [canonicalTwoToTwoSignedLegList, twoToTwoSignedLegList,
    canonicalNondegenerateTwoToTwoLegs] using hperm

/-- Every chosen older presentation yields the same canonical rooted shell,
because the construction depends only on the actual diagram. -/
def externalTwoToTwoPresentationCanonicalMomentumShell
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (_presentation : ExternalTwoToTwoPresentation diagram) :
    TwoToTwoMomentumShell N (outputMomentum diagram) :=
  canonicalTwoToTwoMomentumShell diagram

theorem externalTwoToTwoPresentationCanonicalMomentumShell_unique
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (left right : ExternalTwoToTwoPresentation diagram) :
    externalTwoToTwoPresentationCanonicalMomentumShell left =
      externalTwoToTwoPresentationCanonicalMomentumShell right := rfl

theorem externalTwoToTwoPresentation_reducedExternalModes_eq_actualPermutation
    {N : Nat} {diagram : EffectiveFourWaveDiagram N}
    (presentation : ExternalTwoToTwoPresentation diagram)
    (hsupported : IsTwoVertexMomentumSupported diagram) :
    reducedTwoToTwoExternalModes (outputMomentum diagram)
        (canonicalTwoToTwoFreePair diagram) =
      canonicalTwoToTwoExternalModes diagram :=
  reducedTwoToTwoExternalModes_eq_canonical diagram hsupported
    (externalTwoToTwoPresentation_isExternalTwoToTwoSignSector presentation)

/-! ## Complete actual degenerate-sector count -/

/-- Fixed-output supported actual `2 ↔ 2` diagrams with repeated external
modes.  Unlike `ExternalTwoToTwoPresentation`, this subtype intentionally
allows degeneracy. -/
abbrev FixedOutputDegenerateTwoToTwoDiagram
    (N : Nat) [NeZero N] (output : Site N) :=
  {diagram : FixedOutputSupportedEffectiveFourWaveDiagram N output //
    IsExternalTwoToTwoSignSector diagram.1 ∧
      ¬ Function.Injective (totalFourWaveModes diagram.1)}

noncomputable instance fixedOutputDegenerateTwoToTwoDiagramFintype
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype (FixedOutputDegenerateTwoToTwoDiagram N output) :=
  Fintype.ofFinite _

/-- The 32 insertion-slot/branch decorations, separated from momentum. -/
abbrev EffectiveFourWaveDiscreteDecoration := Fin 2 × (Fin 4 → Fin 2)

/-- A discrete decoration and a degenerate rooted shell. -/
abbrev FixedOutputDegenerateTwoToTwoParameter
    (N : Nat) [NeZero N] (output : Site N) :=
  EffectiveFourWaveDiscreteDecoration ×
    DegenerateTwoToTwoMomentumShell N output

/-- Forget a degenerate diagram down to its decoration and canonical shell. -/
def fixedOutputDegenerateTwoToTwoParameter
    {N : Nat} [NeZero N] {output : Site N}
    (diagram : FixedOutputDegenerateTwoToTwoDiagram N output) :
    FixedOutputDegenerateTwoToTwoParameter N output :=
  ((outerInsertionSlot diagram.1.1, diagram.1.1.2.1),
    ⟨twoToTwoShellFromFree output
        (canonicalTwoToTwoFreePair diagram.1.1), by
      have hdegenerate :=
        (externalModes_not_injective_iff_canonicalFreePair_degenerate
          diagram.1.1 diagram.1.2.1 diagram.2.1).1 diagram.2.2
      simpa [diagram.1.2.2] using hdegenerate⟩)

private theorem totalFourWaveSign_eq_of_branches_eq
    {N : Nat} {left right : EffectiveFourWaveDiagram N}
    (hbranches : left.2.1 = right.2.1) :
    totalFourWaveSign left = totalFourWaveSign right := by
  funext slot
  fin_cases slot <;>
    simp [totalFourWaveSign, diagramBranch, insertedBranch,
      spectatorBranch, innerLeftBranch, innerRightBranch, hbranches]

private theorem canonicalExternalModes_eq_of_data
    {N : Nat} {left right : EffectiveFourWaveDiagram N}
    (houtput : outputMomentum left = outputMomentum right)
    (_hbranches : left.2.1 = right.2.1)
    (hleftSupported : IsTwoVertexMomentumSupported left)
    (hrightSupported : IsTwoVertexMomentumSupported right)
    (hleftSector : IsExternalTwoToTwoSignSector left)
    (hrightSector : IsExternalTwoToTwoSignSector right)
    (hfree : canonicalTwoToTwoFreePair left =
      canonicalTwoToTwoFreePair right) :
    canonicalTwoToTwoExternalModes left =
      canonicalTwoToTwoExternalModes right := by
  have hpositive : canonicalTwoToTwoExternalModes left 1 =
      canonicalTwoToTwoExternalModes right 1 :=
    congrArg Prod.fst hfree
  have hnegativeFirst : canonicalTwoToTwoExternalModes left 2 =
      canonicalTwoToTwoExternalModes right 2 :=
    congrArg Prod.snd hfree
  have hnegativeSecond : canonicalTwoToTwoExternalModes left 3 =
      canonicalTwoToTwoExternalModes right 3 := by
    have hleft := reducedFourth_eq_canonicalSecondNegative left
      hleftSupported hleftSector
    have hright := reducedFourth_eq_canonicalSecondNegative right
      hrightSupported hrightSector
    rw [← hleft, ← hright, houtput, hfree]
  funext slot
  fin_cases slot
  · simpa using houtput
  · exact hpositive
  · exact hnegativeFirst
  · exact hnegativeSecond

theorem fixedOutputDegenerateTwoToTwoParameter_injective
    {N : Nat} [NeZero N] {output : Site N} :
    Function.Injective
      (fixedOutputDegenerateTwoToTwoParameter (N := N) (output := output)) := by
  intro left right hparameter
  have hdecoration :
      (outerInsertionSlot left.1.1, left.1.1.2.1) =
        (outerInsertionSlot right.1.1, right.1.1.2.1) := by
    simpa [fixedOutputDegenerateTwoToTwoParameter] using
      congrArg Prod.fst hparameter
  have hslot : outerInsertionSlot left.1.1 =
      outerInsertionSlot right.1.1 :=
    congrArg
      (fun decoration : EffectiveFourWaveDiscreteDecoration ↦ decoration.1)
      hdecoration
  have hbranches : left.1.1.2.1 = right.1.1.2.1 :=
    congrArg
      (fun decoration : EffectiveFourWaveDiscreteDecoration ↦ decoration.2)
      hdecoration
  have hshell := congrArg Prod.snd hparameter
  have hfree : canonicalTwoToTwoFreePair left.1.1 =
      canonicalTwoToTwoFreePair right.1.1 := by
    have hmodes := congrArg
      (fun shell : DegenerateTwoToTwoMomentumShell N output ↦
        (shellModeOne shell.1, shellModeTwo shell.1)) hshell
    simpa [fixedOutputDegenerateTwoToTwoParameter] using hmodes
  have houtput : outputMomentum left.1.1 = outputMomentum right.1.1 := by
    rw [left.1.2.2, right.1.2.2]
  have hcanonical := canonicalExternalModes_eq_of_data houtput hbranches
    left.1.2.1 right.1.2.1 left.2.1 right.2.1 hfree
  have hsign := totalFourWaveSign_eq_of_branches_eq hbranches
  have hequiv : canonicalTwoToTwoSlotEquiv left.1.1 =
      canonicalTwoToTwoSlotEquiv right.1.1 := by
    unfold canonicalTwoToTwoSlotEquiv
    rw [congrFun hsign 1, congrFun hsign 2]
  have hmodes : totalFourWaveModes left.1.1 =
      totalFourWaveModes right.1.1 := by
    funext slot
    have hslotMode := congrFun hcanonical
      ((canonicalTwoToTwoSlotEquiv left.1.1).symm slot)
    unfold canonicalTwoToTwoExternalModes at hslotMode
    rw [hequiv] at hslotMode
    simpa using hslotMode
  apply Subtype.ext
  apply fixedOutputTwoVertexParameter_injective
  unfold fixedOutputTwoVertexParameter
  have hinnerLeft : innerLeftMomentum left.1.1 =
      innerLeftMomentum right.1.1 := by
    simpa using congrFun hmodes 2
  have hinnerRight : innerRightMomentum left.1.1 =
      innerRightMomentum right.1.1 := by
    simpa using congrFun hmodes 3
  simp only [hslot, hbranches, hinnerLeft, hinnerRight]

/-- Complete subleading count for actual fixed-output degenerate diagrams in
the `2 ↔ 2` sign sector. -/
theorem card_fixedOutputDegenerateTwoToTwoDiagram_le
    (N : Nat) [NeZero N] (output : Site N) :
    Fintype.card (FixedOutputDegenerateTwoToTwoDiagram N output) ≤
      128 * N := by
  calc
    Fintype.card (FixedOutputDegenerateTwoToTwoDiagram N output) ≤
        Fintype.card (FixedOutputDegenerateTwoToTwoParameter N output) :=
      Fintype.card_le_of_injective
        fixedOutputDegenerateTwoToTwoParameter
        fixedOutputDegenerateTwoToTwoParameter_injective
    _ = 32 * Fintype.card (DegenerateTwoToTwoMomentumShell N output) := by
      simp [FixedOutputDegenerateTwoToTwoParameter,
        EffectiveFourWaveDiscreteDecoration]
    _ ≤ 32 * (4 * N) := Nat.mul_le_mul_left 32
      (card_degenerateTwoToTwoMomentumShell_le N output)
    _ = 128 * N := by ring

end

end ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell
