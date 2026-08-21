import Submission.Kakeya.ConvexGeometry.Family
import Submission.Kakeya.ConvexFactoring.IndexPartition

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Cross-multiplied non-concentration conditions

The published Katz--Tao and Frostman conditions are ratios of volumes.  A
`ConvexBody` may be lower-dimensional and hence have zero ambient volume, so
the predicates below use cross-multiplied `ENNReal` inequalities.  Quotient
statements are exposed only as derived lemmas.
-/

/-- Total volume of the members of `F` which are contained in `K`. -/
def containedMass {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (K : ConvexBody Space) : ℝ≥0∞ :=
  ∑ i ∈ containedIndices F K, volume (F i : Set Space)

@[simp]
theorem mem_containedIndices {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (K : ConvexBody Space) (i : ι) :
    i ∈ containedIndices F K ↔ (F i : Set Space) ⊆ (K : Set Space) := by
  classical
  simp [containedIndices]

/-- The old quotient-valued concentration is the quotient of `containedMass`. -/
theorem concentration_eq_containedMass_div {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (K : ConvexBody Space) :
    concentration F K = containedMass F K / volume (K : Set Space) :=
  rfl

/-- Contained mass is monotone in the containing convex body. -/
theorem containedMass_mono {ι : Type*} [Fintype ι]
    {F : ConvexFamily ι} {K L : ConvexBody Space}
    (hKL : (K : Set Space) ⊆ (L : Set Space)) :
    containedMass F K ≤ containedMass F L := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro i hi
  rw [mem_containedIndices] at hi ⊢
  exact hi.trans hKL

/-- Contained mass is bounded by the total indexed family volume. -/
theorem containedMass_le_familyVolume {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (K : ConvexBody Space) :
    containedMass F K ≤ familyVolume F := by
  classical
  unfold containedMass familyVolume
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Contained mass is finite because every member of the finite family is compact. -/
theorem containedMass_lt_top {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (K : ConvexBody Space) :
    containedMass F K < ∞ :=
  (containedMass_le_familyVolume F K).trans_lt (familyVolume_lt_top F)

/-- A zero-volume container can contain only zero-volume members. -/
theorem containedMass_eq_zero_of_volume_eq_zero {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (K : ConvexBody Space)
    (hK : volume (K : Set Space) = 0) :
    containedMass F K = 0 := by
  classical
  unfold containedMass
  apply Finset.sum_eq_zero
  intro i hi
  have hsub : (F i : Set Space) ⊆ (K : Set Space) :=
    (mem_containedIndices F K i).1 hi
  exact nonpos_iff_eq_zero.mp ((measure_mono hsub).trans_eq hK)

/-- Contained mass after retaining only the active indices `s`. -/
noncomputable def containedMassOn {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (s : Finset ι) (K : ConvexBody Space) : ℝ≥0∞ := by
  classical
  exact ∑ i ∈ s ∩ containedIndices F K, volume (F i : Set Space)

@[simp]
theorem containedMassOn_univ {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (K : ConvexBody Space) :
    containedMassOn F Finset.univ K = containedMass F K := by
  classical
  simp [containedMassOn, containedMass]

/-- Retaining fewer indices cannot increase contained mass. -/
theorem containedMassOn_mono {ι : Type*} [Fintype ι]
    {F : ConvexFamily ι} {s t : Finset ι} (hst : s ⊆ t)
    (K : ConvexBody Space) :
    containedMassOn F s K ≤ containedMassOn F t K := by
  classical
  unfold containedMassOn
  apply Finset.sum_le_sum_of_subset
  intro i hi
  rw [Finset.mem_inter] at hi ⊢
  exact ⟨hst hi.1, hi.2⟩

/-- The cross-multiplied Katz--Tao bound for one test body. -/
def IsKatzTaoAt {ι : Type*} [Fintype ι] (C : ℝ≥0∞)
    (F : ConvexFamily ι) (K : ConvexBody Space) : Prop :=
  containedMass F K ≤ C * volume (K : Set Space)

/-- The Katz--Tao non-concentration condition. -/
def IsKatzTao {ι : Type*} [Fintype ι] (C : ℝ≥0∞)
    (F : ConvexFamily ι) : Prop :=
  ∀ K : ConvexBody Space, IsKatzTaoAt C F K

/-- Katz--Tao on an active finite subfamily, without changing index types. -/
def IsKatzTaoOn {ι : Type*} [Fintype ι] (C : ℝ≥0∞)
    (F : ConvexFamily ι) (s : Finset ι) : Prop :=
  ∀ K : ConvexBody Space,
    containedMassOn F s K ≤ C * volume (K : Set Space)

/-- A larger Katz--Tao constant preserves the condition. -/
theorem IsKatzTao.mono {ι : Type*} [Fintype ι]
    {C C' : ℝ≥0∞} {F : ConvexFamily ι}
    (h : IsKatzTao C F) (hCC' : C ≤ C') : IsKatzTao C' F := by
  intro K
  exact (h K).trans (by gcongr)

/-- Katz--Tao is inherited downwards by every active subfamily. -/
theorem IsKatzTao.on {ι : Type*} [Fintype ι]
    {C : ℝ≥0∞} {F : ConvexFamily ι}
    (h : IsKatzTao C F) (s : Finset ι) : IsKatzTaoOn C F s := by
  intro K
  exact (containedMassOn_mono (Finset.subset_univ s) K).trans (by
    simpa [IsKatzTaoAt] using h K)

/-- Katz--Tao on active indices is antitone in the active set. -/
theorem IsKatzTaoOn.anti {ι : Type*} [Fintype ι]
    {C : ℝ≥0∞} {F : ConvexFamily ι} {s t : Finset ι}
    (h : IsKatzTaoOn C F t) (hst : s ⊆ t) : IsKatzTaoOn C F s := by
  intro K
  exact (containedMassOn_mono hst K).trans (h K)

/-- The cross-multiplied definition always implies the familiar quotient bound. -/
theorem IsKatzTaoAt.concentration_le {ι : Type*} [Fintype ι]
    {C : ℝ≥0∞} {F : ConvexFamily ι} {K : ConvexBody Space}
    (h : IsKatzTaoAt C F K) : concentration F K ≤ C := by
  rw [concentration_eq_containedMass_div]
  exact ENNReal.div_le_of_le_mul h

/-- For actual contained mass, the quotient and cross-multiplied Katz--Tao
conditions agree even for zero-volume convex bodies. -/
theorem isKatzTaoAt_iff_concentration_le {ι : Type*} [Fintype ι]
    {C : ℝ≥0∞} {F : ConvexFamily ι} {K : ConvexBody Space} :
    IsKatzTaoAt C F K ↔ concentration F K ≤ C := by
  constructor
  · exact IsKatzTaoAt.concentration_le
  · intro h
    unfold IsKatzTaoAt
    by_cases hK : volume (K : Set Space) = 0
    · rw [containedMass_eq_zero_of_volume_eq_zero F K hK, hK]
      simp
    · rw [concentration_eq_containedMass_div] at h
      exact (ENNReal.div_le_iff hK (K.isCompact.measure_lt_top.ne)).1 h

/-- Global quotient characterization of Katz--Tao. -/
theorem isKatzTao_iff_concentration_le {ι : Type*} [Fintype ι]
    {C : ℝ≥0∞} {F : ConvexFamily ι} :
    IsKatzTao C F ↔ ∀ K : ConvexBody Space, concentration F K ≤ C := by
  simp only [IsKatzTao, isKatzTaoAt_iff_concentration_le]

/-- The cross-multiplied Frostman condition inside a specified convex body.

The first conjunct records the paper's premise that every active member lies
in `K`.  The second is
`Delta(F,K') <= C * Delta(F,K)` with both denominators cleared. -/
def IsFrostmanIn {ι : Type*} [Fintype ι] (C : ℝ≥0∞)
    (F : ConvexFamily ι) (K : ConvexBody Space) : Prop :=
  (∀ i, (F i : Set Space) ⊆ (K : Set Space)) ∧
    ∀ K' : ConvexBody Space, (K' : Set Space) ⊆ (K : Set Space) →
      containedMass F K' * volume (K : Set Space) ≤
        C * containedMass F K * volume (K' : Set Space)

namespace IsFrostmanIn

theorem family_subset {ι : Type*} [Fintype ι]
    {C : ℝ≥0∞} {F : ConvexFamily ι} {K : ConvexBody Space}
    (h : IsFrostmanIn C F K) (i : ι) :
    (F i : Set Space) ⊆ (K : Set Space) :=
  h.1 i

theorem cross_le {ι : Type*} [Fintype ι]
    {C : ℝ≥0∞} {F : ConvexFamily ι} {K K' : ConvexBody Space}
    (h : IsFrostmanIn C F K) (hK' : (K' : Set Space) ⊆ (K : Set Space)) :
    containedMass F K' * volume (K : Set Space) ≤
      C * containedMass F K * volume (K' : Set Space) :=
  h.2 K' hK'

/-- A larger Frostman constant preserves the condition. -/
theorem mono {ι : Type*} [Fintype ι]
    {C C' : ℝ≥0∞} {F : ConvexFamily ι} {K : ConvexBody Space}
    (h : IsFrostmanIn C F K) (hCC' : C ≤ C') :
    IsFrostmanIn C' F K := by
  refine ⟨h.1, fun K' hK' ↦ (h.2 K' hK').trans ?_⟩
  gcongr

/-- Quotient form of a Frostman inequality when both denominators are nonzero. -/
theorem concentration_le_of_volume_ne_zero {ι : Type*} [Fintype ι]
    {C : ℝ≥0∞} {F : ConvexFamily ι} {K K' : ConvexBody Space}
    (h : IsFrostmanIn C F K) (hK' : (K' : Set Space) ⊆ (K : Set Space))
    (hvolK : volume (K : Set Space) ≠ 0)
    (hvolK' : volume (K' : Set Space) ≠ 0) :
    concentration F K' ≤ C * concentration F K := by
  rw [concentration_eq_containedMass_div,
    concentration_eq_containedMass_div]
  rw [ENNReal.div_le_iff hvolK' (K'.isCompact.measure_lt_top.ne)]
  have hdiv : containedMass F K' ≤
      (C * containedMass F K * volume (K' : Set Space)) /
        volume (K : Set Space) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hvolK)
      (Or.inl (K.isCompact.measure_lt_top.ne))).2 (h.2 K' hK')
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- The familiar quotient Frostman inequality.  Zero-volume cases are
discharged from containment, rather than imposed as hypotheses on callers. -/
theorem concentration_le {ι : Type*} [Fintype ι]
    {C : ℝ≥0∞} {F : ConvexFamily ι} {K K' : ConvexBody Space}
    (h : IsFrostmanIn C F K) (hK' : (K' : Set Space) ⊆ (K : Set Space)) :
    concentration F K' ≤ C * concentration F K := by
  by_cases hvolK : volume (K : Set Space) = 0
  · have hvolK' : volume (K' : Set Space) = 0 :=
      nonpos_iff_eq_zero.mp ((measure_mono hK').trans_eq hvolK)
    have hmassK := containedMass_eq_zero_of_volume_eq_zero F K hvolK
    have hmassK' := containedMass_eq_zero_of_volume_eq_zero F K' hvolK'
    simp [concentration_eq_containedMass_div, hvolK, hvolK', hmassK, hmassK']
  · by_cases hvolK' : volume (K' : Set Space) = 0
    · have hmassK' := containedMass_eq_zero_of_volume_eq_zero F K' hvolK'
      simp [concentration_eq_containedMass_div, hvolK', hmassK']
    · exact h.concentration_le_of_volume_ne_zero hK' hvolK hvolK'

end IsFrostmanIn

/-- The cross-multiplied Frostman predicate exactly recovers the paper's
quotient formulation, including lower-dimensional zero-volume bodies. -/
theorem isFrostmanIn_iff_concentration_le {ι : Type*} [Fintype ι]
    {C : ℝ≥0∞} {F : ConvexFamily ι} {K : ConvexBody Space} :
    IsFrostmanIn C F K ↔
      (∀ i, (F i : Set Space) ⊆ (K : Set Space)) ∧
        ∀ K' : ConvexBody Space, (K' : Set Space) ⊆ (K : Set Space) →
          concentration F K' ≤ C * concentration F K := by
  constructor
  · intro h
    exact ⟨h.1, fun K' hK' ↦ h.concentration_le hK'⟩
  · rintro ⟨hcontained, hquotient⟩
    refine ⟨hcontained, fun K' hK' ↦ ?_⟩
    by_cases hvolK : volume (K : Set Space) = 0
    · have hmassK := containedMass_eq_zero_of_volume_eq_zero F K hvolK
      simp [hvolK, hmassK]
    · by_cases hvolK' : volume (K' : Set Space) = 0
      · have hmassK' := containedMass_eq_zero_of_volume_eq_zero F K' hvolK'
        simp [hvolK', hmassK']
      · have hq := hquotient K' hK'
        rw [concentration_eq_containedMass_div,
          concentration_eq_containedMass_div] at hq
        have hmass : containedMass F K' ≤
            (C * (containedMass F K / volume (K : Set Space))) *
              volume (K' : Set Space) :=
          (ENNReal.div_le_iff hvolK' (K'.isCompact.measure_lt_top.ne)).1 hq
        calc
          containedMass F K' * volume (K : Set Space) ≤
              ((C * (containedMass F K / volume (K : Set Space))) *
                volume (K' : Set Space)) * volume (K : Set Space) := by
            gcongr
          _ = C * ((containedMass F K / volume (K : Set Space)) *
                volume (K : Set Space)) * volume (K' : Set Space) := by
            ac_rfl
          _ = C * containedMass F K * volume (K' : Set Space) := by
            rw [ENNReal.div_mul_cancel hvolK (K.isCompact.measure_lt_top.ne)]

/-- A global Katz--Tao estimate yields a Frostman estimate once the ambient
density supplies the displayed normalization.  This is the valid
cross-multiplied relationship; no maximizing body is asserted. -/
theorem IsKatzTao.isFrostmanIn {ι : Type*} [Fintype ι]
    {A C : ℝ≥0∞} {F : ConvexFamily ι} {K : ConvexBody Space}
    (hKT : IsKatzTao A F)
    (hcontained : ∀ i, (F i : Set Space) ⊆ (K : Set Space))
    (hbase : A * volume (K : Set Space) ≤ C * containedMass F K) :
    IsFrostmanIn C F K := by
  refine ⟨hcontained, fun K' _hK' ↦ ?_⟩
  calc
    containedMass F K' * volume (K : Set Space) ≤
        (A * volume (K' : Set Space)) * volume (K : Set Space) :=
      by
        gcongr
        simpa [IsKatzTaoAt] using hKT K'
    _ = (A * volume (K : Set Space)) * volume (K' : Set Space) := by
      ac_rfl
    _ ≤ (C * containedMass F K) * volume (K' : Set Space) :=
      by gcongr
    _ = C * containedMass F K * volume (K' : Set Space) := rfl

/-- Conversely, Frostman plus an ambient density upper bound gives the
corresponding Katz--Tao bound for every test body inside the ambient body. -/
theorem IsFrostmanIn.local_katzTao {ι : Type*} [Fintype ι]
    {C A : ℝ≥0∞} {F : ConvexFamily ι} {K : ConvexBody Space}
    (hF : IsFrostmanIn C F K)
    (hbase : containedMass F K ≤ A * volume (K : Set Space))
    (K' : ConvexBody Space) (hK' : (K' : Set Space) ⊆ (K : Set Space)) :
    containedMass F K' ≤ (C * A) * volume (K' : Set Space) := by
  by_cases hvolK : volume (K : Set Space) = 0
  · have hvolK' : volume (K' : Set Space) = 0 :=
      nonpos_iff_eq_zero.mp ((measure_mono hK').trans_eq hvolK)
    have hmassK' := containedMass_eq_zero_of_volume_eq_zero F K' hvolK'
    simp [hmassK']
  · apply (ENNReal.mul_le_mul_iff_left hvolK
      (K.isCompact.measure_lt_top.ne)).1
    calc
      containedMass F K' * volume (K : Set Space) ≤
          C * containedMass F K * volume (K' : Set Space) := hF.2 K' hK'
      _ ≤ C * (A * volume (K : Set Space)) * volume (K' : Set Space) := by
        gcongr
      _ = ((C * A) * volume (K' : Set Space)) * volume (K : Set Space) := by
        ac_rfl

end

end Submission.Kakeya.ConvexFactoring
