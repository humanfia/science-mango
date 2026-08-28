import ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionChartAdapter

/-!
# The canonical positive Umklapp root lies in the principal zone

For `k₀,k₁ ∈ (0,2π)` and positive transverse discriminant, the
canonical positive-orientation arcsine branch selected by the collision-chart
adapter always produces a root in `(0,2π)`.

The proof splits the external-momentum region at `k₀+k₁=2π`.  Below
that line the structural cosine is positive and the canonical root is the
outer arcsine branch; above it the structural cosine is negative and the
canonical root is the principal branch.  Positive discriminant excludes the
separating line itself.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTCanonicalPositiveRootBrillouin

open Set
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionChartAdapter
open ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.NormalizedResonancePeakKernel
open Filter MeasureTheory Topology

noncomputable section

def umklappStructuralAngle (k₀ k₁ : Real) : Real :=
  (k₀ + k₁) / 4

def umklappDifferenceAngle (k₀ k₁ : Real) : Real :=
  (k₀ - k₁) / 4

theorem umklappDifferenceAngle_mem_Ioo
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi) :
    umklappDifferenceAngle k₀ k₁ ∈
      Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  unfold umklappDifferenceAngle
  constructor <;> linarith

theorem abs_differenceAngle_lt_structuralAngle
    {k₀ k₁ : Real} (hk₀0 : 0 < k₀) (hk₁0 : 0 < k₁) :
    |umklappDifferenceAngle k₀ k₁| <
      umklappStructuralAngle k₀ k₁ := by
  rw [abs_lt]
  unfold umklappDifferenceAngle umklappStructuralAngle
  constructor <;> linarith

theorem umklappResonanceNumerator_pos_in_principal_zone
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi) :
    0 < umklappResonanceNumerator k₀ k₁ := by
  have hstructural := structuralUmklappAngle_mem_Ioo_zero_pi
    hk₀0 hk₀2pi hk₁0 hk₁2pi
  have hdifference := umklappDifferenceAngle_mem_Ioo
    hk₀0 hk₀2pi hk₁0 hk₁2pi
  unfold umklappResonanceNumerator
  unfold umklappDifferenceAngle at hdifference
  exact mul_pos
    (Real.sin_pos_of_pos_of_lt_pi hstructural.1 hstructural.2)
    (Real.cos_pos_of_mem_Ioo hdifference)

theorem umklappResonanceDenominator_pos_of_sum_lt_two_pi
    {k₀ k₁ : Real} (hk₀0 : 0 < k₀) (hk₁0 : 0 < k₁)
    (hsum : k₀ + k₁ < 2 * Real.pi) :
    0 < umklappResonanceDenominator k₀ k₁ := by
  unfold umklappResonanceDenominator
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith

theorem umklappResonanceDenominator_neg_of_two_pi_lt_sum
    {k₀ k₁ : Real}
    (hk₀2pi : k₀ < 2 * Real.pi) (hk₁2pi : k₁ < 2 * Real.pi)
    (hsum : 2 * Real.pi < k₀ + k₁) :
    umklappResonanceDenominator k₀ k₁ < 0 := by
  unfold umklappResonanceDenominator
  exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith)
    (by linarith [Real.pi_pos])

theorem umklappPositiveArcsineBranch_eq_outer_of_sum_lt_two_pi
    {k₀ k₁ : Real} (hk₀0 : 0 < k₀) (hk₁0 : 0 < k₁)
    (hsum : k₀ + k₁ < 2 * Real.pi) :
    umklappPositiveArcsineBranch k₀ k₁ = .outer := by
  have hdenominator :=
    umklappResonanceDenominator_pos_of_sum_lt_two_pi hk₀0 hk₁0 hsum
  simp [umklappPositiveArcsineBranch, hdenominator]

theorem umklappPositiveArcsineBranch_eq_principal_of_two_pi_lt_sum
    {k₀ k₁ : Real}
    (hk₀2pi : k₀ < 2 * Real.pi) (hk₁2pi : k₁ < 2 * Real.pi)
    (hsum : 2 * Real.pi < k₀ + k₁) :
    umklappPositiveArcsineBranch k₀ k₁ = .principal := by
  have hdenominator :=
    umklappResonanceDenominator_neg_of_two_pi_lt_sum
      hk₀2pi hk₁2pi hsum
  simp [umklappPositiveArcsineBranch, not_lt.mpr hdenominator.le]

/-- Exact, readily checkable classification of the positive branch in the
principal external zone.  The lower-sum region is precisely the outer
arcsine branch; no discriminant assumption is needed for this statement. -/
theorem umklappPositiveArcsineBranch_eq_outer_iff_sum_lt_two_pi
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi) :
    umklappPositiveArcsineBranch k₀ k₁ = .outer ↔
      k₀ + k₁ < 2 * Real.pi := by
  constructor
  · intro hbranch
    by_contra hsum
    have hle : 2 * Real.pi ≤ k₀ + k₁ := le_of_not_gt hsum
    rcases hle.eq_or_lt with heq | hlt
    · have hdenominatorZero :
          umklappResonanceDenominator k₀ k₁ = 0 := by
        unfold umklappResonanceDenominator
        rw [← heq]
        rw [show 2 * Real.pi / 4 = Real.pi / 2 by ring]
        exact Real.cos_pi_div_two
      simp [umklappPositiveArcsineBranch, hdenominatorZero] at hbranch
    · have hprincipal :=
        umklappPositiveArcsineBranch_eq_principal_of_two_pi_lt_sum
          hk₀2pi hk₁2pi hlt
      rw [hprincipal] at hbranch
      contradiction
  · exact umklappPositiveArcsineBranch_eq_outer_of_sum_lt_two_pi
      hk₀0 hk₁0

/-- Without imposing transversality, the complementary closed half-zone is
exactly the principal branch (the separating line itself has zero
denominator and is therefore assigned to `principal`). -/
theorem umklappPositiveArcsineBranch_eq_principal_iff_two_pi_le_sum
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi) :
    umklappPositiveArcsineBranch k₀ k₁ = .principal ↔
      2 * Real.pi ≤ k₀ + k₁ := by
  constructor
  · intro hbranch
    by_contra hsum
    have hlower : k₀ + k₁ < 2 * Real.pi := lt_of_not_ge hsum
    have houter :=
      umklappPositiveArcsineBranch_eq_outer_iff_sum_lt_two_pi
        hk₀0 hk₀2pi hk₁0 hk₁2pi
    rw [houter.mpr hlower] at hbranch
    contradiction
  · intro hsum
    rcases hsum.eq_or_lt with heq | hgreater
    · have hdenominatorZero :
          umklappResonanceDenominator k₀ k₁ = 0 := by
        unfold umklappResonanceDenominator
        rw [← heq]
        rw [show 2 * Real.pi / 4 = Real.pi / 2 by ring]
        exact Real.cos_pi_div_two
      simp [umklappPositiveArcsineBranch, hdenominatorZero]
    · exact umklappPositiveArcsineBranch_eq_principal_of_two_pi_lt_sum
        hk₀2pi hk₁2pi hgreater

theorem umklappResonanceRatio_pos_of_sum_lt_two_pi
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hsum : k₀ + k₁ < 2 * Real.pi) :
    0 < umklappResonanceRatio k₀ k₁ := by
  unfold umklappResonanceRatio
  exact div_pos
    (umklappResonanceNumerator_pos_in_principal_zone
      hk₀0 hk₀2pi hk₁0 hk₁2pi)
    (umklappResonanceDenominator_pos_of_sum_lt_two_pi
      hk₀0 hk₁0 hsum)

theorem umklappResonanceRatio_neg_of_two_pi_lt_sum
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hsum : 2 * Real.pi < k₀ + k₁) :
    umklappResonanceRatio k₀ k₁ < 0 := by
  unfold umklappResonanceRatio
  exact div_neg_of_pos_of_neg
    (umklappResonanceNumerator_pos_in_principal_zone
      hk₀0 hk₀2pi hk₁0 hk₁2pi)
    (umklappResonanceDenominator_neg_of_two_pi_lt_sum
      hk₀2pi hk₁2pi hsum)

private theorem cos_difference_gt_cos_structural_of_sum_lt_two_pi
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₁0 : 0 < k₁)
    (hsum : k₀ + k₁ < 2 * Real.pi) :
    Real.cos (umklappStructuralAngle k₀ k₁) <
      Real.cos (umklappDifferenceAngle k₀ k₁) := by
  have habs := abs_differenceAngle_lt_structuralAngle hk₀0 hk₁0
  have hstructuralUpper : umklappStructuralAngle k₀ k₁ ≤ Real.pi := by
    unfold umklappStructuralAngle
    linarith
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
    (abs_nonneg (umklappDifferenceAngle k₀ k₁))
    hstructuralUpper habs
  by_cases hdifference : 0 ≤ umklappDifferenceAngle k₀ k₁
  · simpa [abs_of_nonneg hdifference] using hcos
  · have hdifferenceNeg : umklappDifferenceAngle k₀ k₁ < 0 :=
      lt_of_not_ge hdifference
    rw [abs_of_neg hdifferenceNeg, Real.cos_neg] at hcos
    exact hcos

/-- In the lower-sum region, the outer root falls below `2π` because its
principal arcsine angle is strictly larger than the structural angle. -/
theorem structuralAngle_lt_arcsin_resonanceRatio_of_sum_lt_two_pi
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₁0 : 0 < k₁)
    (hsum : k₀ + k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    umklappStructuralAngle k₀ k₁ <
      Real.arcsin (umklappResonanceRatio k₀ k₁) := by
  have hstructuralMem : umklappStructuralAngle k₀ k₁ ∈
      Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    unfold umklappStructuralAngle
    constructor <;> linarith
  have hratio := umklappResonanceRatio_mem_Ioo hdisc
  apply (Real.lt_arcsin_iff_sin_lt hstructuralMem
    ⟨hratio.1.le, hratio.2.le⟩).2
  have hsinPos : 0 < Real.sin (umklappStructuralAngle k₀ k₁) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · unfold umklappStructuralAngle
      linarith
    · unfold umklappStructuralAngle
      linarith
  have hcosPos : 0 < Real.cos (umklappStructuralAngle k₀ k₁) := by
    apply Real.cos_pos_of_mem_Ioo
    unfold umklappStructuralAngle
    constructor <;> linarith
  have hcos := cos_difference_gt_cos_structural_of_sum_lt_two_pi
    hk₀0 hk₁0 hsum
  unfold umklappResonanceRatio umklappResonanceNumerator
    umklappResonanceDenominator
  unfold umklappStructuralAngle at hsinPos hcosPos hcos ⊢
  unfold umklappDifferenceAngle at hcos
  apply (lt_div_iff₀ hcosPos).2
  nlinarith

theorem external_sum_ne_two_pi_of_discriminant_pos
    {k₀ k₁ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    k₀ + k₁ ≠ 2 * Real.pi := by
  intro hsum
  have hdenominator :=
    umklappResonanceDenominator_ne_zero_of_discriminant_pos hdisc
  apply hdenominator
  unfold umklappResonanceDenominator
  rw [hsum]
  rw [show 2 * Real.pi / 4 = Real.pi / 2 by ring]
  exact Real.cos_pi_div_two

/-- Positive discriminant removes the degenerate separating line, so the
external zone is the disjoint union of its lower- and upper-sum regions. -/
theorem external_sum_lt_or_gt_two_pi_of_discriminant_pos
    {k₀ k₁ : Real}
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    k₀ + k₁ < 2 * Real.pi ∨
      2 * Real.pi < k₀ + k₁ :=
  lt_or_gt_of_ne (external_sum_ne_two_pi_of_discriminant_pos hdisc)

/-- On a transverse shell, the principal branch is exactly the strict
upper-sum region. -/
theorem umklappPositiveArcsineBranch_eq_principal_iff_two_pi_lt_sum
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    umklappPositiveArcsineBranch k₀ k₁ = .principal ↔
      2 * Real.pi < k₀ + k₁ := by
  rw [umklappPositiveArcsineBranch_eq_principal_iff_two_pi_le_sum
    hk₀0 hk₀2pi hk₁0 hk₁2pi]
  constructor
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact False.elim
        ((external_sum_ne_two_pi_of_discriminant_pos hdisc) heq.symm)
  · exact fun hlt ↦ hlt.le

/-- Main region-classified result: the canonical positive-orientation root
always lies in the principal Brillouin zone. -/
theorem canonicalPositiveArcsineRoot_mem_principalZone
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    umklappArcsineRoot (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁ ∈
      Ioo 0 (2 * Real.pi) := by
  have hsumNe := external_sum_ne_two_pi_of_discriminant_pos hdisc
  rcases lt_or_gt_of_ne hsumNe with hsumLower | hsumGreater
  · have hbranch :=
      umklappPositiveArcsineBranch_eq_outer_of_sum_lt_two_pi
        hk₀0 hk₁0 hsumLower
    have hratioPos := umklappResonanceRatio_pos_of_sum_lt_two_pi
      hk₀0 hk₀2pi hk₁0 hk₁2pi hsumLower
    have harcsinUpper := Real.arcsin_lt_pi_div_two.mpr
      (umklappResonanceRatio_mem_Ioo hdisc).2
    have hstructuralArcsin :=
      structuralAngle_lt_arcsin_resonanceRatio_of_sum_lt_two_pi
        hk₀0 hk₁0 hsumLower hdisc
    rw [hbranch]
    unfold umklappArcsineRoot umklappRootFromAngle
      umklappArcsineAngle
    rw [if_pos hratioPos.le]
    constructor
    · linarith [Real.pi_pos]
    · unfold umklappStructuralAngle at hstructuralArcsin
      linarith
  · have hbranch :=
      umklappPositiveArcsineBranch_eq_principal_of_two_pi_lt_sum
        hk₀2pi hk₁2pi hsumGreater
    have hratioNeg := umklappResonanceRatio_neg_of_two_pi_lt_sum
      hk₀0 hk₀2pi hk₁0 hk₁2pi hsumGreater
    have hratio := umklappResonanceRatio_mem_Ioo hdisc
    have harcsinLower := Real.neg_pi_div_two_lt_arcsin.mpr hratio.1
    have harcsinNeg := Real.arcsin_lt_zero.mpr hratioNeg
    rw [hbranch]
    unfold umklappArcsineRoot umklappRootFromAngle
      umklappArcsineAngle
    constructor
    · linarith
    · linarith

theorem canonicalPositiveArcsineRoot_pos
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    0 < umklappArcsineRoot
      (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁ :=
  (canonicalPositiveArcsineRoot_mem_principalZone
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc).1

theorem canonicalPositiveArcsineRoot_lt_two_pi
    {k₀ k₁ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁) :
    umklappArcsineRoot
        (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁ <
      2 * Real.pi :=
  (canonicalPositiveArcsineRoot_mem_principalZone
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc).2

/-- Collision-limit endpoint with both root-membership assumptions removed. -/
theorem tendsto_canonicalPositiveUmklappCollisionChart_principalZone
    {k₀ k₁ : Real} {mark density : Real → Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (data : UmklappArcsineCollisionMeasureData
      (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁ mark density) :
    Tendsto
      (fun T : Real ↦ ∫ z in
        umklappArcsineLocalLeft (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁..
          umklappArcsineLocalRight
            (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁,
        normalizedFiniteTimeResonanceKernel
          (umklappReducedFourWaveMismatch k₀ k₁ z) T * mark z)
      atTop
      (nhds (mark (umklappArcsineRoot
          (umklappPositiveArcsineBranch k₀ k₁) k₀ k₁) /
        (2 * Real.sqrt (umklappTransverseDiscriminant k₀ k₁)))) :=
  tendsto_canonicalPositiveUmklappArcsineCollisionChart
    hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc
      (canonicalPositiveArcsineRoot_pos
        hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc)
      (canonicalPositiveArcsineRoot_lt_two_pi
        hk₀0 hk₀2pi hk₁0 hk₁2pi hdisc)
      data

end

end ArchonPhysics.EqualMassPeriodicFPUTCanonicalPositiveRootBrillouin
