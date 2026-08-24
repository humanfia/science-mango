import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
import Mathlib.Data.Real.Basic

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensClassificationV1

open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1

noncomputable section

/-!
# Geometric classification of selected first-generation lenses

For a side of a lens, Marcus--Tardos call the side positive precisely when
the opposite open side lies in the interior of the corresponding curve.
Thus the two literal side carriers and the two literal curve interiors
determine the class; no face/moon/inverse label is supplied by a caller.
-/

/-- Literal carrier data for the fixed-slot lenses attached to unordered
curve pairs.  `entryKey` is the actual parameter at which the selected side
is first encountered in the chosen positive orientation of a curve. -/
structure SelectedFixedSlotLensGeometry
    (point curve : Type*) [DecidableEq curve] (curves : Finset curve) where
  firstCurve : FirstGenerationCurvePair curves -> FirstGenerationCurve curves
  secondCurve : FirstGenerationCurvePair curves -> FirstGenerationCurve curves
  pair_eq : forall p, p.1 = s(firstCurve p, secondCurve p)
  firstOpenSide : FirstGenerationCurvePair curves -> Set point
  secondOpenSide : FirstGenerationCurvePair curves -> Set point
  curveInterior : FirstGenerationCurve curves -> Set point
  entryKey : FirstGenerationCurvePair curves ->
    FirstGenerationCurve curves -> Real

variable {point curve : Type*} [DecidableEq curve]
variable {curves : Finset curve}

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Positivity of the side lying on the first oriented curve. -/
def firstSidePositive
    (D : SelectedFixedSlotLensGeometry point curve curves)
    (p : FirstGenerationCurvePair curves) : Prop :=
  D.secondOpenSide p ⊆ D.curveInterior (D.firstCurve p)

/-- Positivity of the side lying on the second oriented curve. -/
def secondSidePositive
    (D : SelectedFixedSlotLensGeometry point curve curves)
    (p : FirstGenerationCurvePair curves) : Prop :=
  D.firstOpenSide p ⊆ D.curveInterior (D.secondCurve p)

/-- The Marcus--Tardos class is computed from the two positivity bits:
`++` is a lens-face, exactly one `+` is a moon-face, and `--` is an
inverse-face. -/
noncomputable def selectedProperLensKind
    (D : SelectedFixedSlotLensGeometry point curve curves)
    (p : FirstGenerationCurvePair curves) : ProperLensKind :=
  if firstSidePositive D p then
    if secondSidePositive D p then ProperLensKind.lensFace
    else ProperLensKind.moonFace
  else if secondSidePositive D p then ProperLensKind.moonFace
  else ProperLensKind.inverseFace

theorem selectedProperLensKind_eq_lensFace_iff
    (D : SelectedFixedSlotLensGeometry point curve curves)
    (p : FirstGenerationCurvePair curves) :
    selectedProperLensKind D p = ProperLensKind.lensFace ↔
      firstSidePositive D p ∧ secondSidePositive D p := by
  classical
  by_cases hfirst : firstSidePositive D p <;>
    by_cases hsecond : secondSidePositive D p <;>
      simp [selectedProperLensKind, hfirst, hsecond]

theorem selectedProperLensKind_eq_moonFace_iff
    (D : SelectedFixedSlotLensGeometry point curve curves)
    (p : FirstGenerationCurvePair curves) :
    selectedProperLensKind D p = ProperLensKind.moonFace ↔
      (firstSidePositive D p ∧ ¬ secondSidePositive D p) ∨
      (¬ firstSidePositive D p ∧ secondSidePositive D p) := by
  classical
  by_cases hfirst : firstSidePositive D p <;>
    by_cases hsecond : secondSidePositive D p <;>
      simp [selectedProperLensKind, hfirst, hsecond]

theorem selectedProperLensKind_eq_inverseFace_iff
    (D : SelectedFixedSlotLensGeometry point curve curves)
    (p : FirstGenerationCurvePair curves) :
    selectedProperLensKind D p = ProperLensKind.inverseFace ↔
      ¬ firstSidePositive D p ∧ ¬ secondSidePositive D p := by
  classical
  by_cases hfirst : firstSidePositive D p <;>
    by_cases hsecond : secondSidePositive D p <;>
      simp [selectedProperLensKind, hfirst, hsecond]

/-- For a moon-face choose its unique positive side as host.  For the two
symmetric classes choose the first oriented side. -/
noncomputable def selectedLensHost
    (D : SelectedFixedSlotLensGeometry point curve curves)
    (p : FirstGenerationCurvePair curves) : FirstGenerationCurve curves :=
  if ¬ firstSidePositive D p ∧ secondSidePositive D p then
    D.secondCurve p
  else D.firstCurve p

/-- The curve paired with `selectedLensHost`. -/
noncomputable def selectedLensNeighbor
    (D : SelectedFixedSlotLensGeometry point curve curves)
    (p : FirstGenerationCurvePair curves) : FirstGenerationCurve curves :=
  if ¬ firstSidePositive D p ∧ secondSidePositive D p then
    D.firstCurve p
  else D.secondCurve p

theorem selectedLensHost_positive_of_moonFace
    (D : SelectedFixedSlotLensGeometry point curve curves)
    (p : FirstGenerationCurvePair curves)
    (hmoon : selectedProperLensKind D p = ProperLensKind.moonFace) :
    (selectedLensHost D p = D.firstCurve p ∧ firstSidePositive D p) ∨
      (selectedLensHost D p = D.secondCurve p ∧ secondSidePositive D p) := by
  classical
  rw [selectedProperLensKind_eq_moonFace_iff] at hmoon
  rcases hmoon with hfirst | hsecond
  · left
    exact ⟨by simp [selectedLensHost, hfirst.1, hfirst.2], hfirst.1⟩
  · right
    exact ⟨by simp [selectedLensHost, hsecond.1, hsecond.2], hsecond.2⟩

/-- The chosen host and neighbor still recover the literal unordered pair. -/
theorem pair_eq_selectedLensHost_selectedLensNeighbor
    (D : SelectedFixedSlotLensGeometry point curve curves)
    (p : FirstGenerationCurvePair curves) :
    p.1 = s(selectedLensHost D p, selectedLensNeighbor D p) := by
  classical
  rw [D.pair_eq p]
  by_cases hsecondHost :
      ¬ firstSidePositive D p ∧ secondSidePositive D p
  · simp [selectedLensHost, selectedLensNeighbor, hsecondHost]
  · simp [selectedLensHost, selectedLensNeighbor, hsecondHost]

/-- Membership rule for the three list families.  Symmetric lens- and
inverse-faces occur at both sides; a moon-face occurs only at its positive
side. -/
def selectedLensAssignedTo
    (D : SelectedFixedSlotLensGeometry point curve curves)
    (k : ProperLensKind) (c : FirstGenerationCurve curves)
    (p : FirstGenerationCurvePair curves) : Prop :=
  selectedProperLensKind D p = k ∧
    if k = ProperLensKind.moonFace then selectedLensHost D p = c
    else c = D.firstCurve p ∨ c = D.secondCurve p

theorem selectedLensAssignedTo_chosenHost
    (D : SelectedFixedSlotLensGeometry point curve curves)
    (p : FirstGenerationCurvePair curves) :
    selectedLensAssignedTo D (selectedProperLensKind D p)
      (selectedLensHost D p) p := by
  classical
  refine ⟨rfl, ?_⟩
  by_cases hmoon :
      selectedProperLensKind D p = ProperLensKind.moonFace
  · simp [hmoon]
  · rw [if_neg hmoon]
    by_cases hsecondHost :
        ¬ firstSidePositive D p ∧ secondSidePositive D p
    · exact Or.inr (by simp [selectedLensHost, hsecondHost])
    · exact Or.inl (by simp [selectedLensHost, hsecondHost])

#print axioms SelectedFixedSlotLensGeometry
#print axioms firstSidePositive
#print axioms secondSidePositive
#print axioms selectedProperLensKind
#print axioms selectedProperLensKind_eq_lensFace_iff
#print axioms selectedProperLensKind_eq_moonFace_iff
#print axioms selectedProperLensKind_eq_inverseFace_iff
#print axioms selectedLensHost
#print axioms selectedLensNeighbor
#print axioms selectedLensHost_positive_of_moonFace
#print axioms pair_eq_selectedLensHost_selectedLensNeighbor
#print axioms selectedLensAssignedTo
#print axioms selectedLensAssignedTo_chosenHost

end

end FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensClassificationV1
