import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T9-A9: arrangements of a hexadifferentiated `α`-cyclodextrin

The source asks for arrangements of six distinct functional groups on the six
primary `CH₂OH` sites of an `α`-cyclodextrin.  A placement is therefore a
bijection from the six sites to the six functional groups.  Since the molecule
is cyclic, two placements that differ only by a rotation of the six sites
represent the same arrangement.  Reflections are deliberately not identified:
the source's counting argument identifies the six rotations and divides `6!`
by `6`.
-/

namespace IChO2026Problems.T9A9

/-- The six primary `CH₂OH` sites of an `α`-cyclodextrin, in cyclic order. -/
private abbrev AlphaCDPrimarySite := Fin 6

/-- Rotation of an `α`-cyclodextrin primary site by a specified cyclic shift. -/
private def rotatePrimarySite
    (shift site : AlphaCDPrimarySite) : AlphaCDPrimarySite :=
  ⟨(site.val + shift.val) % 6, Nat.mod_lt _ (by omega)⟩

/-- A hexadifferentiated placement assigns every one of the six distinct
functional groups to exactly one primary `CH₂OH` site. -/
private abbrev LinearArrangement (functionalGroup : Type u) :=
  AlphaCDPrimarySite ≃ functionalGroup

/-- Two placements are chemically the same circular arrangement precisely
when one is obtained from the other by a rotation of the `α`-CD ring. -/
private def rotationallyEquivalent {functionalGroup : Type u}
    (left right : LinearArrangement functionalGroup) : Prop :=
  ∃ shift : AlphaCDPrimarySite, ∀ site : AlphaCDPrimarySite,
    left (rotatePrimarySite shift site) = right site

/-- The quotient relation implementing the source's identification of all
six rotations of a cyclic placement. -/
private def circularArrangementSetoid (functionalGroup : Type u) :
    Setoid (LinearArrangement functionalGroup) where
  r := rotationallyEquivalent
  iseqv := by
    let inverseShift : AlphaCDPrimarySite → AlphaCDPrimarySite := fun shift =>
      ⟨(6 - shift.val) % 6, Nat.mod_lt _ (by omega)⟩
    have rotate_inverse (shift site : AlphaCDPrimarySite) :
        rotatePrimarySite shift (rotatePrimarySite (inverseShift shift) site) = site := by
      fin_cases shift <;> fin_cases site <;> simp [inverseShift, rotatePrimarySite]
    let combinedShift : AlphaCDPrimarySite → AlphaCDPrimarySite → AlphaCDPrimarySite :=
      fun first second => ⟨(first.val + second.val) % 6, Nat.mod_lt _ (by omega)⟩
    have rotate_combined (first second site : AlphaCDPrimarySite) :
        rotatePrimarySite (combinedShift first second) site =
          rotatePrimarySite first (rotatePrimarySite second site) := by
      fin_cases first <;> fin_cases second <;> fin_cases site <;>
        simp [combinedShift, rotatePrimarySite]
    refine ⟨?_, ?_, ?_⟩
    · intro arrangement
      refine ⟨0, ?_⟩
      intro site
      fin_cases site <;> rfl
    · intro left right h
      rcases h with ⟨shift, hshift⟩
      refine ⟨inverseShift shift, ?_⟩
      intro site
      rw [← hshift (rotatePrimarySite (inverseShift shift) site), rotate_inverse]
    · intro left middle right hleft hright
      rcases hleft with ⟨first, hfirst⟩
      rcases hright with ⟨second, hsecond⟩
      refine ⟨combinedShift first second, ?_⟩
      intro site
      rw [rotate_combined, hfirst, hsecond]

/-- A physical arrangement of the six distinct primary-site modifications,
with no distinguished starting glucopyranose unit. -/
private abbrev CircularArrangement (functionalGroup : Type u) :=
  Quotient (circularArrangementSetoid functionalGroup)

/-- The set of circular arrangements is finite whenever the functional-group
type is finite.  Classical decidability is used only to enumerate quotient
classes, not to impose any chemical conclusion. -/
private noncomputable instance circularArrangementFintype
    (functionalGroup : Type u) [Fintype functionalGroup] [DecidableEq functionalGroup] :
    Fintype (CircularArrangement functionalGroup) := by
  classical
  exact Quotient.fintype (circularArrangementSetoid functionalGroup)

/-- Before identifying rotations, the six primary sites admit `6! = 720`
bijective placements by the six distinct functional groups. -/
private theorem linear_placement_count
    (functionalGroup : Type u) [Fintype functionalGroup] [DecidableEq functionalGroup]
    (hgroups : Fintype.card functionalGroup = 6) :
    Fintype.card (LinearArrangement functionalGroup) = 720 := by
  let e : AlphaCDPrimarySite ≃ functionalGroup :=
    Fintype.equivOfCardEq (by simpa [AlphaCDPrimarySite] using hgroups.symm)
  calc
    Fintype.card (LinearArrangement functionalGroup) =
        (Fintype.card AlphaCDPrimarySite).factorial := Fintype.card_equiv e
    _ = 720 := by norm_num [AlphaCDPrimarySite]

/-- T9-A9.  A hexadifferentiated `α`-cyclodextrin has 120 possible
arrangements of its functional groups on the primary `CH₂OH` sites. -/
theorem number_of_hexadifferentiated_alphaCD_arrangements
    (functionalGroup : Type u) [Fintype functionalGroup] [DecidableEq functionalGroup]
    (hgroups : Fintype.card functionalGroup = 6) :
    Fintype.card (CircularArrangement functionalGroup) = 120 := by
  let groupEquiv : functionalGroup ≃ Fin 6 :=
    Fintype.equivOfCardEq (by simpa using hgroups)
  let placementEquiv : LinearArrangement functionalGroup ≃ LinearArrangement (Fin 6) :=
    Equiv.equivCongr (Equiv.refl AlphaCDPrimarySite) groupEquiv
  have preserves_rotations (left right : LinearArrangement functionalGroup) :
      (circularArrangementSetoid functionalGroup) left right ↔
        (circularArrangementSetoid (Fin 6))
          (placementEquiv left) (placementEquiv right) := by
    change rotationallyEquivalent left right ↔
      rotationallyEquivalent (placementEquiv left) (placementEquiv right)
    constructor
    · rintro ⟨shift, hshift⟩
      refine ⟨shift, ?_⟩
      intro site
      simpa [placementEquiv] using congrArg groupEquiv (hshift site)
    · rintro ⟨shift, hshift⟩
      refine ⟨shift, ?_⟩
      intro site
      apply groupEquiv.injective
      simpa [placementEquiv] using hshift site
  letI : DecidableRel
      (fun left right : LinearArrangement (Fin 6) =>
        (circularArrangementSetoid (Fin 6)) left right) := by
    intro left right
    change Decidable (rotationallyEquivalent left right)
    exact Fintype.decidableExistsFintype
  letI : Fintype (CircularArrangement (Fin 6)) :=
    Quotient.fintype (circularArrangementSetoid (Fin 6))
  calc
    Fintype.card (CircularArrangement functionalGroup) =
        Fintype.card (CircularArrangement (Fin 6)) :=
      Fintype.card_congr (Quotient.congr placementEquiv preserves_rotations)
    _ = 120 := by
      let inverseShift : AlphaCDPrimarySite → AlphaCDPrimarySite := fun shift =>
        ⟨(6 - shift.val) % 6, Nat.mod_lt _ (by omega)⟩
      have rotate_inverse (shift site : AlphaCDPrimarySite) :
          rotatePrimarySite shift (rotatePrimarySite (inverseShift shift) site) = site := by
        fin_cases shift <;> fin_cases site <;> simp [inverseShift, rotatePrimarySite]
      have rotate_rotate (first second site : AlphaCDPrimarySite) :
          rotatePrimarySite (rotatePrimarySite first second) site =
            rotatePrimarySite first (rotatePrimarySite second site) := by
        fin_cases first <;> fin_cases second <;> fin_cases site <;> rfl
      have rotate_zero (shift : AlphaCDPrimarySite) :
          rotatePrimarySite shift 0 = shift := by
        fin_cases shift <;> rfl
      have zero_rotate (site : AlphaCDPrimarySite) :
          rotatePrimarySite 0 site = site := by
        fin_cases site <;> rfl
      let rotateEquiv : AlphaCDPrimarySite → AlphaCDPrimarySite ≃ AlphaCDPrimarySite := fun shift =>
        { toFun := rotatePrimarySite shift
          invFun := rotatePrimarySite (inverseShift shift)
          left_inv := by
            intro site
            fin_cases shift <;> fin_cases site <;> simp [inverseShift, rotatePrimarySite]
          right_inv := rotate_inverse shift }
      let fixedArrangement :=
        { arrangement : LinearArrangement (Fin 6) // arrangement 0 = 0 }
      let normalize : LinearArrangement (Fin 6) → fixedArrangement := fun arrangement =>
        ⟨(rotateEquiv (arrangement.symm 0)).trans arrangement, by
          change arrangement (rotatePrimarySite (arrangement.symm 0) 0) = 0
          rw [rotate_zero, arrangement.apply_symm_apply]⟩
      have normalize_respects
          (left right : LinearArrangement (Fin 6))
          (h : (circularArrangementSetoid (Fin 6)) left right) :
          normalize left = normalize right := by
        change rotationallyEquivalent left right at h
        rcases h with ⟨shift, hshift⟩
        apply Subtype.ext
        apply Equiv.ext
        intro site
        change left (rotatePrimarySite (left.symm 0) site) =
          right (rotatePrimarySite (right.symm 0) site)
        have hzero := hshift (right.symm 0)
        rw [right.apply_symm_apply] at hzero
        have hrotation : rotatePrimarySite shift (right.symm 0) = left.symm 0 := by
          apply left.injective
          rw [left.apply_symm_apply]
          exact hzero
        rw [← hshift]
        apply congrArg left
        rw [← hrotation]
        exact rotate_rotate shift (right.symm 0) site
      let quotientToFixed : CircularArrangement (Fin 6) → fixedArrangement :=
        Quotient.lift normalize normalize_respects
      let fixedToQuotient : fixedArrangement → CircularArrangement (Fin 6) :=
        fun arrangement => Quotient.mk (circularArrangementSetoid (Fin 6)) arrangement.1
      have leftInverse : Function.LeftInverse fixedToQuotient quotientToFixed := by
        intro circular
        refine Quotient.inductionOn circular ?_
        intro arrangement
        change Quotient.mk (circularArrangementSetoid (Fin 6)) (normalize arrangement).1 =
          Quotient.mk (circularArrangementSetoid (Fin 6)) arrangement
        apply Quotient.sound
        change rotationallyEquivalent (normalize arrangement).1 arrangement
        refine ⟨inverseShift (arrangement.symm 0), ?_⟩
        intro site
        change arrangement
            (rotatePrimarySite (arrangement.symm 0)
              (rotatePrimarySite (inverseShift (arrangement.symm 0)) site)) =
          arrangement site
        rw [rotate_inverse]
      have rightInverse : Function.RightInverse fixedToQuotient quotientToFixed := by
        intro arrangement
        apply Subtype.ext
        apply Equiv.ext
        intro site
        change arrangement.1 (rotatePrimarySite (arrangement.1.symm 0) site) = arrangement.1 site
        have hzero : arrangement.1.symm 0 = 0 := by
          apply arrangement.1.injective
          rw [arrangement.1.apply_symm_apply, arrangement.2]
        rw [hzero, zero_rotate]
      let quotientNormalize : CircularArrangement (Fin 6) ≃ fixedArrangement :=
        ⟨quotientToFixed, fixedToQuotient, leftInverse, rightInverse⟩
      let zeroSet : Set (Fin 6) := {0}
      let complementEquiv : (↑zeroSetᶜ : Type) ≃ { site : Fin 6 // site ≠ 0 } :=
        Equiv.subtypeEquivRight (by
          intro site
          simp [zeroSet])
      let fixedAsSetEquiv : fixedArrangement ≃
          { arrangement : LinearArrangement (Fin 6) //
              ∀ site : (↑zeroSet : Type), arrangement site = site } :=
        Equiv.subtypeEquivRight (by
          intro arrangement
          constructor
          · intro h site
            have hsite : site.1 = 0 := by
              simpa only [zeroSet, Set.mem_singleton_iff] using site.property
            simpa [hsite] using h
          · intro h
            simpa [zeroSet] using h ⟨0, by simp [zeroSet]⟩)
      calc
        Fintype.card (CircularArrangement (Fin 6)) = Fintype.card fixedArrangement :=
          Fintype.card_congr quotientNormalize
        _ = Fintype.card { arrangement : LinearArrangement (Fin 6) //
            ∀ site : (↑zeroSet : Type), arrangement site = site } :=
          Fintype.card_congr fixedAsSetEquiv
        _ = Fintype.card ((↑zeroSetᶜ : Type) ≃ (↑zeroSetᶜ : Type)) :=
          Fintype.card_congr (Equiv.Set.compl (Equiv.refl (↑zeroSet : Type)))
        _ = (Fintype.card (↑zeroSetᶜ : Type)).factorial :=
          Fintype.card_equiv (Equiv.refl (↑zeroSetᶜ : Type))
        _ = 120 := by
          have complement_card : Fintype.card (↑zeroSetᶜ : Type) = 5 := by
            rw [Fintype.card_congr complementEquiv]
            decide
          rw [complement_card]
          norm_num

end IChO2026Problems.T9A9
