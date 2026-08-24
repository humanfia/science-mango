import FamilyStickyRandomFiniteMaximalCellCodeV1
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace FamilyStickyCinematicL32FiniteMetricMaximalCoverV1

open FamilyStickyRandomFiniteMaximalCellCodeV1

noncomputable section

/-!
# A finite maximal fixed-radius metric cover

This is the purely finite cover used after the norm critical scale has been
placed in one global dyadic bin.  Maximality constructs the centres and their
covering code.  Metric containment in a triple-radius ball is proved from an
actual intersection witness.
-/

variable {alpha : Type*} [DecidableEq alpha]

/-- Membership-bearing points of a finite ambient family. -/
abbrev FiniteMetricMember (family : Finset alpha) := {f // f ∈ family}

/-- Separation at one fixed global scale. -/
def finiteMetricSeparated (family : Finset alpha)
    (distance : alpha → alpha → Real) (scale : Real)
    (f g : FiniteMetricMember family) : Prop :=
  scale ≤ distance f.1 g.1

set_option linter.unusedSectionVars false in
theorem finiteMetricSeparated_symm
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (scale : Real) (hsymm : ∀ f g, distance f g = distance g f) :
    Std.Symm (finiteMetricSeparated family distance scale) := by
  constructor
  intro f g hfg
  rw [finiteMetricSeparated, hsymm]
  exact hfg

/-- A canonical maximal separated centre family. -/
noncomputable def finiteMetricMaximalCover
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (scale : Real) (hsymm : ∀ f g, distance f g = distance g f) :
    MaximalSeparatedCells (finiteMetricSeparated family distance scale) :=
  Classical.choice (exists_maximalSeparatedCells
    (finiteMetricSeparated family distance scale)
    (finiteMetricSeparated_symm family distance scale hsymm))

/-- The selected centres, with membership proofs forgotten. -/
noncomputable def finiteMetricCoverCenters
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (scale : Real) (hsymm : ∀ f g, distance f g = distance g f) :
    Finset alpha := by
  classical
  exact (finiteMetricMaximalCover family distance scale hsymm).cells.image
    Subtype.val

/-- The centre assigned by maximality to one ambient member. -/
noncomputable def finiteMetricCoverCode
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (scale : Real) (hsymm : ∀ f g, distance f g = distance g f)
    (f : FiniteMetricMember family) : alpha :=
  (finiteMetricMaximalCover family distance scale hsymm).code f |>.1.1

theorem finiteMetricCoverCenters_subset
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (scale : Real) (hsymm : ∀ f g, distance f g = distance g f) :
    finiteMetricCoverCenters family distance scale hsymm ⊆ family := by
  classical
  intro center hcenter
  rw [finiteMetricCoverCenters, Finset.mem_image] at hcenter
  obtain ⟨member, _hmember, rfl⟩ := hcenter
  exact member.2

theorem finiteMetricCoverCode_mem_centers
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (scale : Real) (hsymm : ∀ f g, distance f g = distance g f)
    (f : FiniteMetricMember family) :
    finiteMetricCoverCode family distance scale hsymm f ∈
      finiteMetricCoverCenters family distance scale hsymm := by
  classical
  rw [finiteMetricCoverCenters, Finset.mem_image]
  let C := finiteMetricMaximalCover family distance scale hsymm
  exact ⟨(C.code f).1, (C.code f).2, by simp [finiteMetricCoverCode, C]⟩

/-- Every ambient member lies strictly inside the scale-ball of its code.
The equality branch uses only the metric self bound. -/
theorem distance_finiteMetricCoverCode_lt
    (family : Finset alpha) (distance : alpha → alpha → Real)
    {scale : Real} (hsymm : ∀ f g, distance f g = distance g f)
    (hself : ∀ f, f ∈ family → distance f f < scale)
    (f : FiniteMetricMember family) :
    distance f.1 (finiteMetricCoverCode family distance scale hsymm f) <
      scale := by
  let C := finiteMetricMaximalCover family distance scale hsymm
  rcases C.eq_or_not_separated_code f with heq | hnot
  · have hvalue : f.1 = (C.code f).1.1 := congrArg Subtype.val heq
    change distance f.1 (C.code f).1.1 < scale
    rw [← hvalue]
    exact hself f.1 f.2
  · change distance f.1 (C.code f).1.1 < scale
    exact lt_of_not_ge (by
      simpa only [finiteMetricSeparated] using hnot)

/-- Distinct selected centres are separated at the fixed global scale. -/
theorem finiteMetricCoverCenters_pairwise_separated
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (scale : Real) (hsymm : ∀ f g, distance f g = distance g f) :
    ∀ f, f ∈ finiteMetricCoverCenters family distance scale hsymm →
      ∀ g, g ∈ finiteMetricCoverCenters family distance scale hsymm →
        f ≠ g → scale ≤ distance f g := by
  classical
  intro f hf g hg hfg
  rw [finiteMetricCoverCenters, Finset.mem_image] at hf hg
  obtain ⟨fm, hfm, rfl⟩ := hf
  obtain ⟨gm, hgm, rfl⟩ := hg
  have hmembers : fm ≠ gm := by
    intro h
    exact hfg (congrArg Subtype.val h)
  exact (finiteMetricMaximalCover family distance scale hsymm).pairwise
    hfm hgm hmembers

/-- A nonempty ambient family has a nonempty maximal centre family. -/
theorem finiteMetricCoverCenters_nonempty
    (family : Finset alpha) (distance : alpha → alpha → Real)
    (scale : Real) (hsymm : ∀ f g, distance f g = distance g f)
    (hfamily : family.Nonempty) :
    (finiteMetricCoverCenters family distance scale hsymm).Nonempty := by
  classical
  obtain ⟨f, hf⟩ := hfamily
  exact ⟨finiteMetricCoverCode family distance scale hsymm ⟨f, hf⟩,
    finiteMetricCoverCode_mem_centers family distance scale hsymm ⟨f, hf⟩⟩

/-- A closed finite-family ball. -/
def finiteFamilyMetricBall (family : Finset alpha)
    (distance : alpha → alpha → Real) (radius : Real) (center : alpha) :
    Finset alpha :=
  family.filter fun f => distance f center ≤ radius

set_option linter.unusedSectionVars false in
/-- If a radius-`localScale` ball meets a radius-`globalScale` ball and
`localScale ≤ globalScale`, the former lies in the triple global ball. -/
theorem finiteFamilyMetricBall_subset_three_of_intersects
    (family : Finset alpha) (distance : alpha → alpha → Real)
    {localScale globalScale : Real} (localCenter globalCenter witness : alpha)
    (hsymm : ∀ f g, distance f g = distance g f)
    (htriangle : ∀ f center g,
      distance f g ≤ distance f center + distance center g)
    (hscale : localScale ≤ globalScale)
    (hwLocal : distance witness localCenter ≤ localScale)
    (hwGlobal : distance witness globalCenter ≤ globalScale) :
    finiteFamilyMetricBall family distance localScale localCenter ⊆
      finiteFamilyMetricBall family distance (3 * globalScale) globalCenter := by
  intro f hf
  have hfData : f ∈ family ∧ distance f localCenter ≤ localScale := by
    simpa only [finiteFamilyMetricBall, Finset.mem_filter] using hf
  rw [finiteFamilyMetricBall, Finset.mem_filter]
  refine ⟨hfData.1, ?_⟩
  calc
    distance f globalCenter ≤
        distance f localCenter + distance localCenter globalCenter :=
      htriangle _ _ _
    _ ≤ distance f localCenter +
        (distance localCenter witness + distance witness globalCenter) :=
      add_le_add_right (htriangle localCenter witness globalCenter) (distance f localCenter)
    _ = distance f localCenter +
        (distance witness localCenter + distance witness globalCenter) := by
      rw [hsymm localCenter witness]
    _ ≤ localScale + (localScale + globalScale) :=
      add_le_add hfData.2 (add_le_add hwLocal hwGlobal)
    _ ≤ globalScale + (globalScale + globalScale) :=
      add_le_add hscale (add_le_add hscale le_rfl)
    _ = 3 * globalScale := by
      ring

#print axioms finiteMetricMaximalCover
#print axioms finiteMetricCoverCenters
#print axioms finiteMetricCoverCode
#print axioms finiteMetricCoverCenters_subset
#print axioms finiteMetricCoverCode_mem_centers
#print axioms distance_finiteMetricCoverCode_lt
#print axioms finiteMetricCoverCenters_pairwise_separated
#print axioms finiteMetricCoverCenters_nonempty
#print axioms finiteFamilyMetricBall_subset_three_of_intersects

end

end FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
