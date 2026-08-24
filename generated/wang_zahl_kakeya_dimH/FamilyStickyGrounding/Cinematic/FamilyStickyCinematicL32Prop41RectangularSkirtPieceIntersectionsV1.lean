import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RectangularSkirtPathV1

set_option autoImplicit false

open Function Set

namespace FamilyStickyCinematicL32Prop41RectangularSkirtPieceIntersectionsV1

open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41RectangularSkirtPathV1

noncomputable section

def skirtGraph (f : Real -> Real) (A B : Real) : Set (Real × Real) :=
  graphArc f (Icc A B)

def skirtRightTop (f : Real -> Real) (B depth : Real) : Set (Real × Real) :=
  graphArc (fun _ => f B) (Icc B (B + depth))

def skirtRightWall (f : Real -> Real) (B M depth : Real) : Set (Real × Real) :=
  verticalSegment (B + depth) (f B) (skirtBottom M depth)

def skirtFloor (A B M depth : Real) : Set (Real × Real) :=
  graphArc (fun _ => skirtBottom M depth) (Icc (A - depth) (B + depth))

def skirtLeftWall (f : Real -> Real) (A M depth : Real) : Set (Real × Real) :=
  verticalSegment (A - depth) (skirtBottom M depth) (f A)

def skirtLeftTop (f : Real -> Real) (A depth : Real) : Set (Real × Real) :=
  graphArc (fun _ => f A) (Icc (A - depth) A)

def skirtPrefixTwo (f : Real -> Real) (A B depth : Real) : Set (Real × Real) :=
  skirtGraph f A B ∪ skirtRightTop f B depth

def skirtPrefixThree (f : Real -> Real) (A B M depth : Real) : Set (Real × Real) :=
  skirtPrefixTwo f A B depth ∪ skirtRightWall f B M depth

def skirtPrefixFour (f : Real -> Real) (A B M depth : Real) : Set (Real × Real) :=
  skirtPrefixThree f A B M depth ∪ skirtFloor A B M depth

def skirtPrefixFive (f : Real -> Real) (A B M depth : Real) : Set (Real × Real) :=
  skirtPrefixFour f A B M depth ∪ skirtLeftWall f A M depth

theorem skirtGraph_inter_rightTop
    (f : Real -> Real) (A B depth : Real) (hAB : A < B) (hdepth : 0 < depth) :
    skirtGraph f A B ∩ skirtRightTop f B depth = {(f B, B)} := by
  ext q
  constructor
  · rintro ⟨⟨hqI, hqf⟩, ⟨hqJ, hqB⟩⟩
    have htheta : q.2 = B := le_antisymm hqI.2 hqJ.1
    have hvalue : q.1 = f B := by simpa [htheta] using hqf
    exact Prod.ext hvalue htheta
  · intro hq
    rw [mem_singleton_iff] at hq
    subst q
    exact ⟨⟨⟨hAB.le, le_rfl⟩, rfl⟩,
      ⟨⟨le_rfl, by linarith⟩, rfl⟩⟩

theorem skirtPrefixTwo_inter_rightWall
    (f : Real -> Real) (A B M depth : Real)
    (hdepth : 0 < depth) :
    skirtPrefixTwo f A B depth ∩ skirtRightWall f B M depth =
      {(f B, B + depth)} := by
  ext q
  constructor
  · rintro ⟨hq, hwall⟩
    rcases hq with hgraph | htop
    · exfalso
      exact (not_lt_of_ge hgraph.1.2) (by simpa [hwall.1] using add_lt_add_left hdepth B)
    · have htheta : q.2 = B + depth := hwall.1
      have hvalue : q.1 = f B := htop.2
      exact Prod.ext hvalue htheta
  · intro hq
    rw [mem_singleton_iff] at hq
    subst q
    exact ⟨Or.inr ⟨⟨by linarith, le_rfl⟩, rfl⟩,
      ⟨rfl, left_mem_uIcc⟩⟩

theorem skirtPrefixThree_inter_floor
    (f : Real -> Real) (A B M depth : Real)
    (hAB : A < B) (hdepth : 0 < depth)
    (hgraphLower : forall theta, theta ∈ Icc A B -> -M <= f theta) :
    skirtPrefixThree f A B M depth ∩ skirtFloor A B M depth =
      {(skirtBottom M depth, B + depth)} := by
  ext q
  constructor
  · rintro ⟨hq, hfloor⟩
    rcases hq with hprefix | hwall
    · rcases hprefix with hgraph | htop
      · have hlower := hgraphLower q.2 hgraph.1
        have heq : f q.2 = skirtBottom M depth :=
          hgraph.2.symm.trans hfloor.2
        exfalso
        rw [heq, skirtBottom] at hlower
        linarith
      · have hlower := hgraphLower B ⟨hAB.le, le_rfl⟩
        have heq : f B = skirtBottom M depth :=
          htop.2.symm.trans hfloor.2
        exfalso
        rw [heq, skirtBottom] at hlower
        linarith
    · exact Prod.ext hfloor.2 hwall.1
  · intro hq
    rw [mem_singleton_iff] at hq
    subst q
    exact ⟨Or.inr ⟨rfl, right_mem_uIcc⟩,
      ⟨⟨by linarith, le_rfl⟩, rfl⟩⟩

theorem skirtPrefixFour_inter_leftWall
    (f : Real -> Real) (A B M depth : Real)
    (hAB : A < B) (hdepth : 0 < depth) :
    skirtPrefixFour f A B M depth ∩ skirtLeftWall f A M depth =
      {(skirtBottom M depth, A - depth)} := by
  ext q
  constructor
  · rintro ⟨hq, hleft⟩
    rcases hq with hprefix | hfloor
    · rcases hprefix with hprefix | hright
      · rcases hprefix with hgraph | htop
        · exfalso
          have htheta := hgraph.1.1
          rw [hleft.1] at htheta
          linarith
        · exfalso
          have htheta := htop.1.1
          rw [hleft.1] at htheta
          linarith
      · exfalso
        linarith [hleft.1, hright.1]
    · exact Prod.ext hfloor.2 hleft.1
  · intro hq
    rw [mem_singleton_iff] at hq
    subst q
    exact ⟨Or.inr ⟨⟨le_rfl, by linarith⟩, rfl⟩,
      ⟨rfl, left_mem_uIcc⟩⟩

theorem skirtPrefixFive_inter_leftTop
    (f : Real -> Real) (A B M depth : Real)
    (hAB : A < B) (hdepth : 0 < depth)
    (hgraphLower : forall theta, theta ∈ Icc A B -> -M <= f theta) :
    skirtPrefixFive f A B M depth ∩ skirtLeftTop f A depth =
      {(f A, A), (f A, A - depth)} := by
  ext q
  constructor
  · rintro ⟨hq, htopLeft⟩
    rcases hq with hprefix | hleft
    · rcases hprefix with hprefix | hfloor
      · rcases hprefix with hprefix | hright
        · rcases hprefix with hgraph | htopRight
          · left
            have htheta : q.2 = A := le_antisymm htopLeft.1.2 hgraph.1.1
            exact Prod.ext htopLeft.2 htheta
          · exfalso
            linarith [htopRight.1.1, htopLeft.1.2]
        · exfalso
          linarith [hright.1, htopLeft.1.2]
      · have hlower := hgraphLower A ⟨le_rfl, hAB.le⟩
        have heq : f A = skirtBottom M depth :=
          htopLeft.2.symm.trans hfloor.2
        exfalso
        rw [heq, skirtBottom] at hlower
        linarith
    · right
      exact Prod.ext htopLeft.2 hleft.1
  · intro hq
    rcases hq with hstart | hjoint
    · subst q
      exact ⟨Or.inl (Or.inl (Or.inl (Or.inl
        ⟨⟨le_rfl, hAB.le⟩, rfl⟩))),
        ⟨⟨by linarith, le_rfl⟩, rfl⟩⟩
    · rw [mem_singleton_iff] at hjoint
      subst q
      exact ⟨Or.inr ⟨rfl, right_mem_uIcc⟩,
        ⟨⟨le_rfl, by linarith⟩, rfl⟩⟩

#print axioms skirtGraph_inter_rightTop
#print axioms skirtPrefixTwo_inter_rightWall
#print axioms skirtPrefixThree_inter_floor
#print axioms skirtPrefixFour_inter_leftWall
#print axioms skirtPrefixFive_inter_leftTop

end

end FamilyStickyCinematicL32Prop41RectangularSkirtPieceIntersectionsV1
