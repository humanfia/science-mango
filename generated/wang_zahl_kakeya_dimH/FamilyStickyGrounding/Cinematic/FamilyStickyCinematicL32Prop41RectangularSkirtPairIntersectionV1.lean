import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RectangularSkirtPieceIntersectionsV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41RectangularSkirtPairIntersectionV1

open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41RectangularSkirtPathV1
open FamilyStickyCinematicL32Prop41RectangularSkirtPieceIntersectionsV1

noncomputable section

/-!
# Exact pair intersections for rectangular skirts

The five artificial skirt pieces are separated from the original graph arc.
For increasing depths and increasing left endpoint values, every artificial
pair intersection is excluded except the single right horizontal--vertical
crossing which occurs precisely when the right endpoint order reverses.
-/

def skirtExterior
    (f : Real -> Real) (A B M depth : Real) : Set (Real × Real) :=
  graphArc (fun _ => f A) (Icc (A - depth) A) ∪
    (graphArc (fun _ => f B) (Icc B (B + depth)) ∪
      (verticalSegment (A - depth) (skirtBottom M depth) (f A) ∪
        (verticalSegment (B + depth) (skirtBottom M depth) (f B) ∪
          graphArc (fun _ => skirtBottom M depth)
            (Icc (A - depth) (B + depth)))))

theorem rectangularSkirtCurve_eq_graph_union_exterior
    (f : Real -> Real) (A B M depth : Real) :
    rectangularSkirtCurve f A B M depth =
      skirtGraph f A B ∪ skirtExterior f A B M depth := by
  ext q
  simp only [rectangularSkirtCurve, skirtGraph, skirtExterior,
    skirtBottom, mem_union]
  tauto

theorem skirtGraph_inter_skirtExterior_eq_empty
    (f g : Real -> Real) (A B M depth : Real)
    (hdepth : 0 < depth)
    (hleft : f A ≠ g A) (hright : f B ≠ g B)
    (hfLower : forall theta, theta ∈ Icc A B -> -M <= f theta) :
    skirtGraph f A B ∩ skirtExterior g A B M depth = ∅ := by
  ext q
  constructor
  · rintro ⟨hf, hg⟩
    rcases hg with hg | hg | hg | hg | hg
    · have htheta : q.2 = A := le_antisymm hg.1.2 hf.1.1
      exact (hleft (by simpa [htheta] using hf.2.symm.trans hg.2))
    · have htheta : q.2 = B := le_antisymm hf.1.2 hg.1.1
      exact (hright (by simpa [htheta] using hf.2.symm.trans hg.2))
    · have htheta := hf.1.1
      rw [hg.1] at htheta
      linarith
    · have htheta := hf.1.2
      rw [hg.1] at htheta
      linarith
    · have hlower := hfLower q.2 hf.1
      have heq : f q.2 = skirtBottom M depth := hf.2.symm.trans hg.2
      rw [heq, skirtBottom] at hlower
      linarith
  · simp

theorem skirtExterior_inter_skirtGraph_eq_empty
    (f g : Real -> Real) (A B M depth : Real)
    (hdepth : 0 < depth)
    (hleft : f A ≠ g A) (hright : f B ≠ g B)
    (hgLower : forall theta, theta ∈ Icc A B -> -M <= g theta) :
    skirtExterior f A B M depth ∩ skirtGraph g A B = ∅ := by
  rw [inter_comm]
  exact skirtGraph_inter_skirtExterior_eq_empty g f A B M depth
    hdepth hleft.symm hright.symm hgLower

/-- The full five-by-five exterior case split.  Every exterior intersection
is the right horizontal--vertical point, and its existence forces reversal
of the right endpoint order. -/
theorem mem_skirtExterior_inter_skirtExterior
    (f g : Real -> Real) (A B M d e : Real)
    (hAB : A < B) (hd : 0 < d) (hde : d < e)
    (hleft : f A < g A) (hrightNe : f B ≠ g B)
    (hfLower : forall theta, theta ∈ Icc A B -> -M <= f theta)
    (hgLower : forall theta, theta ∈ Icc A B -> -M <= g theta)
    {q : Real × Real}
    (hq : q ∈ skirtExterior f A B M d ∩ skirtExterior g A B M e) :
    q = (g B, B + d) ∧ g B <= f B := by
  rcases hq.1 with hf | hf | hf | hf | hf <;>
    rcases hq.2 with hg | hg | hg | hg | hg
  · linarith [hf.2, hg.2]
  · linarith [hf.1.2, hg.1.1, hAB]
  · linarith [hf.1.1, hg.1]
  · linarith [hf.1.2, hg.1, hAB]
  · have hlower := hfLower A ⟨le_rfl, hAB.le⟩
    have heq : f A = skirtBottom M e := hf.2.symm.trans hg.2
    rw [heq, skirtBottom] at hlower
    linarith
  · linarith [hf.1.1, hg.1.2, hAB]
  · exact False.elim (hrightNe (hf.2.symm.trans hg.2))
  · linarith [hf.1.1, hg.1, hAB]
  · linarith [hf.1.2, hg.1]
  · have hlower := hfLower B ⟨hAB.le, le_rfl⟩
    have heq : f B = skirtBottom M e := hf.2.symm.trans hg.2
    rw [heq, skirtBottom] at hlower
    linarith
  · have hvalue : q.1 = g A := hg.2
    have hbottom : skirtBottom M d <= f A := by
      rw [skirtBottom]
      linarith [hfLower A ⟨le_rfl, hAB.le⟩]
    change q.2 = A - d ∧ q.1 ∈ uIcc (skirtBottom M d) (f A) at hf
    rw [uIcc_of_le hbottom] at hf
    have hupper : q.1 <= f A := hf.2.2
    rw [hvalue] at hupper
    linarith
  · have htheta : q.2 = A - d := hf.1
    linarith [hg.1.1]
  · linarith [hf.1, hg.1]
  · linarith [hf.1, hg.1, hAB]
  · have hbottom : skirtBottom M d <= f A := by
      rw [skirtBottom]
      linarith [hfLower A ⟨le_rfl, hAB.le⟩]
    change q.2 = A - d ∧ q.1 ∈ uIcc (skirtBottom M d) (f A) at hf
    rw [uIcc_of_le hbottom] at hf
    have hvalue : q.1 = skirtBottom M e := hg.2
    have hfloorLower := hf.2.1
    rw [hvalue] at hfloorLower
    simp only [skirtBottom] at hfloorLower
    linarith
  · have htheta : q.2 = B + d := hf.1
    linarith [hg.1.2, hAB]
  · have htheta : q.2 = B + d := hf.1
    have hvalue : q.1 = g B := hg.2
    have hbottom : skirtBottom M d <= f B := by
      rw [skirtBottom]
      linarith [hfLower B ⟨hAB.le, le_rfl⟩]
    change q.2 = B + d ∧ q.1 ∈ uIcc (skirtBottom M d) (f B) at hf
    rw [uIcc_of_le hbottom] at hf
    have hupper : q.1 <= f B := hf.2.2
    exact ⟨Prod.ext hvalue htheta, by simpa [hvalue] using hupper⟩
  · linarith [hf.1, hg.1, hAB]
  · linarith [hf.1, hg.1]
  · have hbottom : skirtBottom M d <= f B := by
      rw [skirtBottom]
      linarith [hfLower B ⟨hAB.le, le_rfl⟩]
    change q.2 = B + d ∧ q.1 ∈ uIcc (skirtBottom M d) (f B) at hf
    rw [uIcc_of_le hbottom] at hf
    have hvalue : q.1 = skirtBottom M e := hg.2
    have hfloorLower := hf.2.1
    rw [hvalue] at hfloorLower
    simp only [skirtBottom] at hfloorLower
    linarith
  · have hlower := hgLower A ⟨le_rfl, hAB.le⟩
    have heq : g A = skirtBottom M d := hg.2.symm.trans hf.2
    rw [heq, skirtBottom] at hlower
    linarith
  · have hlower := hgLower B ⟨hAB.le, le_rfl⟩
    have heq : g B = skirtBottom M d := hg.2.symm.trans hf.2
    rw [heq, skirtBottom] at hlower
    linarith
  · have htheta : q.2 = A - e := hg.1
    linarith [hf.1.1]
  · have htheta : q.2 = B + e := hg.1
    linarith [hf.1.2]
  · have heq : skirtBottom M d = skirtBottom M e := hf.2.symm.trans hg.2
    simp only [skirtBottom] at heq
    linarith

theorem skirtExterior_inter_skirtExterior_eq_singleton
    (f g : Real -> Real) (A B M d e : Real)
    (hAB : A < B) (hd : 0 < d) (hde : d < e)
    (hleft : f A < g A) (hright : g B < f B)
    (hfLower : forall theta, theta ∈ Icc A B -> -M <= f theta)
    (hgLower : forall theta, theta ∈ Icc A B -> -M <= g theta) :
    skirtExterior f A B M d ∩ skirtExterior g A B M e =
      {(g B, B + d)} := by
  ext q
  constructor
  · intro hq
    exact (mem_skirtExterior_inter_skirtExterior f g A B M d e hAB hd hde
      hleft (ne_of_gt hright) hfLower hgLower hq).1
  · intro hq
    rw [mem_singleton_iff] at hq
    subst q
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ?_))), Or.inr (Or.inl ?_)⟩
    · refine ⟨rfl, ?_⟩
      apply mem_uIcc_of_le
      · have hlower := hgLower B ⟨hAB.le, le_rfl⟩
        rw [skirtBottom]
        linarith
      · exact hright.le
    · exact ⟨⟨by linarith, by linarith⟩, rfl⟩

theorem skirtExterior_inter_skirtExterior_eq_empty
    (f g : Real -> Real) (A B M d e : Real)
    (hAB : A < B) (hd : 0 < d) (hde : d < e)
    (hleft : f A < g A) (hright : f B < g B)
    (hfLower : forall theta, theta ∈ Icc A B -> -M <= f theta)
    (hgLower : forall theta, theta ∈ Icc A B -> -M <= g theta) :
    skirtExterior f A B M d ∩ skirtExterior g A B M e = ∅ := by
  ext q
  constructor
  · intro hq
    have hle := (mem_skirtExterior_inter_skirtExterior f g A B M d e hAB hd hde
      hleft (ne_of_lt hright) hfLower hgLower hq).2
    exact False.elim (not_le_of_gt hright hle)
  · simp

theorem rectangularSkirtCurve_inter_eq_graph_inter_of_same_endpoint_order
    (f g : Real -> Real) (A B M d e : Real)
    (hAB : A < B) (hd : 0 < d) (he : 0 < e) (hde : d < e)
    (hleft : f A < g A) (hright : f B < g B)
    (hfLower : forall theta, theta ∈ Icc A B -> -M <= f theta)
    (hgLower : forall theta, theta ∈ Icc A B -> -M <= g theta) :
    rectangularSkirtCurve f A B M d ∩ rectangularSkirtCurve g A B M e =
      skirtGraph f A B ∩ skirtGraph g A B := by
  rw [rectangularSkirtCurve_eq_graph_union_exterior,
    rectangularSkirtCurve_eq_graph_union_exterior]
  ext q
  constructor
  · rintro ⟨hf, hg⟩
    rcases hf with hf | hf <;> rcases hg with hg | hg
    · exact ⟨hf, hg⟩
    · have : q ∈ (∅ : Set (Real × Real)) := by
        rw [← skirtGraph_inter_skirtExterior_eq_empty f g A B M e he
          (ne_of_lt hleft) (ne_of_lt hright) hfLower]
        exact ⟨hf, hg⟩
      simp at this
    · have : q ∈ (∅ : Set (Real × Real)) := by
        rw [← skirtExterior_inter_skirtGraph_eq_empty f g A B M d hd
          (ne_of_lt hleft) (ne_of_lt hright) hgLower]
        exact ⟨hf, hg⟩
      simp at this
    · have : q ∈ (∅ : Set (Real × Real)) := by
        rw [← skirtExterior_inter_skirtExterior_eq_empty f g A B M d e hAB hd hde
          hleft hright hfLower hgLower]
        exact ⟨hf, hg⟩
      simp at this
  · rintro ⟨hf, hg⟩
    exact ⟨Or.inl hf, Or.inl hg⟩

theorem rectangularSkirtCurve_inter_eq_graph_inter_union_singleton_of_reversed_endpoint_order
    (f g : Real -> Real) (A B M d e : Real)
    (hAB : A < B) (hd : 0 < d) (he : 0 < e) (hde : d < e)
    (hleft : f A < g A) (hright : g B < f B)
    (hfLower : forall theta, theta ∈ Icc A B -> -M <= f theta)
    (hgLower : forall theta, theta ∈ Icc A B -> -M <= g theta) :
    rectangularSkirtCurve f A B M d ∩ rectangularSkirtCurve g A B M e =
      (skirtGraph f A B ∩ skirtGraph g A B) ∪ {(g B, B + d)} := by
  rw [rectangularSkirtCurve_eq_graph_union_exterior,
    rectangularSkirtCurve_eq_graph_union_exterior]
  ext q
  constructor
  · rintro ⟨hf, hg⟩
    rcases hf with hf | hf <;> rcases hg with hg | hg
    · exact Or.inl ⟨hf, hg⟩
    · have : q ∈ (∅ : Set (Real × Real)) := by
        rw [← skirtGraph_inter_skirtExterior_eq_empty f g A B M e he
          (ne_of_lt hleft) (ne_of_gt hright) hfLower]
        exact ⟨hf, hg⟩
      simp at this
    · have : q ∈ (∅ : Set (Real × Real)) := by
        rw [← skirtExterior_inter_skirtGraph_eq_empty f g A B M d hd
          (ne_of_lt hleft) (ne_of_gt hright) hgLower]
        exact ⟨hf, hg⟩
      simp at this
    · exact Or.inr (by
        rw [← skirtExterior_inter_skirtExterior_eq_singleton f g A B M d e
          hAB hd hde hleft hright hfLower hgLower]
        exact ⟨hf, hg⟩)
  · rintro (hq | hq)
    · exact ⟨Or.inl hq.1, Or.inl hq.2⟩
    · have hq' : q ∈ skirtExterior f A B M d ∩ skirtExterior g A B M e := by
        rw [skirtExterior_inter_skirtExterior_eq_singleton f g A B M d e
          hAB hd hde hleft hright hfLower hgLower]
        exact hq
      exact ⟨Or.inr hq'.1, Or.inr hq'.2⟩

#print axioms rectangularSkirtCurve_eq_graph_union_exterior
#print axioms skirtGraph_inter_skirtExterior_eq_empty
#print axioms skirtExterior_inter_skirtGraph_eq_empty
#print axioms mem_skirtExterior_inter_skirtExterior
#print axioms skirtExterior_inter_skirtExterior_eq_singleton
#print axioms skirtExterior_inter_skirtExterior_eq_empty
#print axioms rectangularSkirtCurve_inter_eq_graph_inter_of_same_endpoint_order
#print axioms rectangularSkirtCurve_inter_eq_graph_inter_union_singleton_of_reversed_endpoint_order

end

end FamilyStickyCinematicL32Prop41RectangularSkirtPairIntersectionV1
