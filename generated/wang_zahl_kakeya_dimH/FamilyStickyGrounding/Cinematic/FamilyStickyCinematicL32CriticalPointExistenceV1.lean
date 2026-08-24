import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalPointGrowthV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32CriticalPointExistenceV1

open FamilyStickyCinematicL32SublevelIntervalV1
open FamilyStickyCinematicL32CriticalPointGrowthV1

/-!
# Existence and uniqueness of the cinematic critical point

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(1a).  Starting from the minimizing parameter `thetaDelta`, the
paper uses smallness of `h'(thetaDelta)` and a nonvanishing curvature bound
to find a unique zero of `h'` nearby.

Here the boundary signs are not assumed.  Explicit buffer inequalities

`eta <= kappa * (thetaDelta - A)` and
`eta <= kappa * (B - thetaDelta)`

combine with `|q(thetaDelta)| <= eta` and `kappa <= |q'|` to produce the
boundary signs by the mean value theorem.  IVT then gives a zero and strict
monotonicity gives uniqueness.
-/

/-- A continuous function with opposite weak signs at the endpoints has a
zero in the closed interval. -/
theorem exists_zero_of_opposite_boundary_signs
    (q : Real -> Real) {A B : Real}
    (hAB : A <= B) (hqContinuous : ContinuousOn q (Icc A B))
    (hboundary : (q A <= 0 ∧ 0 <= q B) ∨
      (q B <= 0 ∧ 0 <= q A)) :
    ∃ theta ∈ Icc A B, q theta = 0 := by
  rcases hboundary with hforward | hreverse
  · obtain ⟨theta, htheta, hzero⟩ :=
      intermediate_value_Icc hAB hqContinuous
        (show (0 : Real) ∈ Icc (q A) (q B) from hforward)
    exact ⟨theta, htheta, hzero⟩
  · obtain ⟨theta, htheta, hzero⟩ :=
      intermediate_value_Icc' hAB hqContinuous
        (show (0 : Real) ∈ Icc (q B) (q A) from hreverse)
    exact ⟨theta, htheta, hzero⟩

/-- Positive derivative separation, a small anchor value, and explicit
endpoint buffers produce a unique zero. -/
theorem buffered_small_value_existsUnique_zero_of_deriv_lower
    (q q1 : Real -> Real) {A B thetaDelta eta kappa : Real}
    (hthetaDelta : thetaDelta ∈ Icc A B) (hkappa : 0 < kappa)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt q (q1 z) z)
    (hderivLower : forall z, z ∈ Icc A B -> kappa <= q1 z)
    (hanchor : |q thetaDelta| <= eta)
    (hleftBuffer : eta <= kappa * (thetaDelta - A))
    (hrightBuffer : eta <= kappa * (B - thetaDelta)) :
    ∃! theta : Real, theta ∈ Icc A B ∧ q theta = 0 := by
  have hAB : A <= B := hthetaDelta.1.trans hthetaDelta.2
  have hleftSubset : Icc A thetaDelta ⊆ Icc A B :=
    Icc_subset_Icc le_rfl hthetaDelta.2
  have hrightSubset : Icc thetaDelta B ⊆ Icc A B :=
    Icc_subset_Icc hthetaDelta.1 le_rfl
  have hleftGrowth := mul_interval_length_le_function_sub_of_deriv_lower
    q q1 hthetaDelta.1
    (fun z hz => hderiv z (hleftSubset hz))
    (fun z hz => hderivLower z (hleftSubset hz))
  have hrightGrowth := mul_interval_length_le_function_sub_of_deriv_lower
    q q1 hthetaDelta.2
    (fun z hz => hderiv z (hrightSubset hz))
    (fun z hz => hderivLower z (hrightSubset hz))
  have hanchorBounds := abs_le.1 hanchor
  have hleftSign : q A <= 0 := by
    nlinarith
  have hrightSign : 0 <= q B := by
    nlinarith
  have hqContinuous : ContinuousOn q (Icc A B) :=
    HasDerivAt.continuousOn hderiv
  obtain ⟨theta, htheta, hzero⟩ :=
    exists_zero_of_opposite_boundary_signs q hAB hqContinuous
      (Or.inl ⟨hleftSign, hrightSign⟩)
  have hstrict : StrictMonoOn q (Icc A B) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos
      (convex_Icc A B) hqContinuous
    · intro z hz
      exact (hderiv z (interior_subset hz)).hasDerivWithinAt
    · intro z hz
      exact hkappa.trans_le (hderivLower z (interior_subset hz))
  refine ⟨theta, ⟨htheta, hzero⟩, ?_⟩
  intro y hy
  apply hstrict.injOn hy.1 htheta
  rw [hy.2, hzero]

/-- Callback-free orientation-independent version.  Continuity and the
absolute derivative lower bound decide the derivative sign internally. -/
theorem buffered_small_value_existsUnique_zero_of_abs_deriv_lower
    (q q1 : Real -> Real) {A B thetaDelta eta kappa : Real}
    (hthetaDelta : thetaDelta ∈ Icc A B) (hkappa : 0 < kappa)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt q (q1 z) z)
    (hq1Continuous : ContinuousOn q1 (Icc A B))
    (hderivLower : forall z, z ∈ Icc A B -> kappa <= |q1 z|)
    (hanchor : |q thetaDelta| <= eta)
    (hleftBuffer : eta <= kappa * (thetaDelta - A))
    (hrightBuffer : eta <= kappa * (B - thetaDelta)) :
    ∃! theta : Real, theta ∈ Icc A B ∧ q theta = 0 := by
  have hAB : A <= B := hthetaDelta.1.trans hthetaDelta.2
  rcases continuous_fixed_sign_of_abs_lower_on_Icc
      q1 hAB hkappa hq1Continuous hderivLower with hpositive | hnegative
  · exact buffered_small_value_existsUnique_zero_of_deriv_lower
      q q1 hthetaDelta hkappa hderiv hpositive hanchor
      hleftBuffer hrightBuffer
  · obtain ⟨theta, htheta, hunique⟩ :=
      buffered_small_value_existsUnique_zero_of_deriv_lower
        (-q) (-q1) hthetaDelta hkappa
        (fun z hz => (hderiv z hz).neg)
        (fun z hz => by
          change kappa <= -q1 z
          linarith [hnegative z hz])
        (show |(-q) thetaDelta| <= eta by
          change |-q thetaDelta| <= eta
          simpa only [abs_neg] using hanchor)
        hleftBuffer hrightBuffer
    refine ⟨theta, ⟨htheta.1, ?_⟩, ?_⟩
    · have hzero : -q theta = 0 := by
        simpa only [Pi.neg_apply] using htheta.2
      linarith
    · intro y hy
      apply hunique y
      refine ⟨hy.1, ?_⟩
      change -q y = 0
      rw [hy.2, neg_zero]

#print axioms exists_zero_of_opposite_boundary_signs
#print axioms buffered_small_value_existsUnique_zero_of_deriv_lower
#print axioms buffered_small_value_existsUnique_zero_of_abs_deriv_lower

end FamilyStickyCinematicL32CriticalPointExistenceV1
