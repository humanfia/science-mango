import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ContinuousTransverseRootParityV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41OrderedExactTwoRootSelectionV1

open FamilyStickyCinematicL32Prop41ContinuousTransverseRootParityV1

/-!
# Selecting the ordered exact two-root output

The perturbation step in PYZ Proposition 4.1 first makes a pair of curves
intersect, while the cinematic geometry supplies at most two transverse
roots and equal nonzero endpoint signs.  The existing parity theorem then
says that the root carrier has cardinality zero or two.

This file performs the missing deterministic selection step.  Nonemptiness
rules out the zero-root branch; the two remaining roots are named, ordered,
and their carrier is identified with the literal two-point set.  No
existence, transversality, or root-cardinality conclusion is assumed in a
repackaged form.
-/

/-- A nonempty finite transverse root carrier with equal endpoint signs and
at most two roots consists of exactly two ordered roots. -/
theorem exists_ordered_exact_two_roots_of_nonempty_same_endpoint_sign
    (h : Real -> Real) {A B : Real}
    (hAB : A < B)
    (hcontinuous : ContinuousOn h (Icc A B))
    (hcard :
      {theta | theta ∈ Icc A B ∧ h theta = 0}.encard <= (2 : Nat))
    (hnonempty :
      {theta | theta ∈ Icc A B ∧ h theta = 0}.Nonempty)
    (hsame : 0 < h A * h B)
    (htransverse : forall theta, theta ∈ Icc A B -> h theta = 0 ->
      exists derivative : Real,
        HasDerivAt h derivative theta ∧ derivative ≠ 0) :
    ∃ thetaLeft thetaRight,
      thetaLeft < thetaRight ∧
      thetaLeft ∈ Icc A B ∧ h thetaLeft = 0 ∧
      thetaRight ∈ Icc A B ∧ h thetaRight = 0 ∧
      {theta | theta ∈ Icc A B ∧ h theta = 0} =
        {thetaLeft, thetaRight} := by
  let roots : Set Real :=
    {theta | theta ∈ Icc A B ∧ h theta = 0}
  have hfiniteCard : roots.Finite ∧ roots.ncard <= 2 := by
    apply Set.encard_le_coe_iff_finite_ncard_le.mp
    simpa only [roots] using hcard
  have hparity : roots.ncard = 0 ∨ roots.ncard = 2 := by
    simpa only [roots] using
      rootSet_ncard_eq_zero_or_two_of_same_endpoint_sign
        h hAB hcontinuous hfiniteCard.2 hsame htransverse
  have hnonempty' : roots.Nonempty := by
    simpa only [roots] using hnonempty
  rcases hparity with hzero | htwo
  · have hempty : roots = ∅ :=
      (Set.ncard_eq_zero hfiniteCard.1).mp hzero
    exact (hnonempty'.ne_empty hempty).elim
  · obtain ⟨x, y, hxy, hroots⟩ := Set.ncard_eq_two.mp htwo
    have hx : x ∈ roots := by
      rw [hroots]
      simp
    have hy : y ∈ roots := by
      rw [hroots]
      simp
    rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
    · exact ⟨x, y, hxylt, hx.1, hx.2, hy.1, hy.2, by
        simpa only [roots] using hroots⟩
    · refine ⟨y, x, hyxlt, hy.1, hy.2, hx.1, hx.2, ?_⟩
      change roots = {y, x}
      rw [hroots]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact or_comm

#print axioms exists_ordered_exact_two_roots_of_nonempty_same_endpoint_sign

end FamilyStickyCinematicL32Prop41OrderedExactTwoRootSelectionV1
