import Submission.Kakeya.ConvexFactoring.JointTubeFactoring

open Set
open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring.JointTubeFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
variable {δ ρ : ℝ≥0}

/-- The base-two logarithm of an assigned fine-fiber cardinality.
Its range has `log₂(card ι) + 1` values. -/
def fiberLogCardLabel (active : Finset ι) (parent : ι → κ) (k : κ) :
    Fin (Nat.log 2 (Fintype.card ι) + 1) :=
  ⟨Nat.log 2 ((rawIndexFactorization active parent).fiber k).card, by
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    exact Finset.card_le_card (Finset.subset_univ _)⟩

/-- Efficient parents in one base-two fiber-cardinality bucket. -/
def efficientLogCardBucket (fine : UniformTubeFamily δ ι)
    (coarse : UniformTubeFamily ρ κ) (active : Finset ι)
    (parent : ι → κ) (A L : ℝ≥0∞)
    (b : Fin (Nat.log 2 (Fintype.card ι) + 1)) : Finset κ :=
  dyadicFiber (efficientParents fine coarse active parent A L)
    (fiberLogCardLabel active parent) b

/-- Membership in a logarithmic bucket identifies the logarithm of the
actual assigned fiber cardinality. -/
theorem efficientLogCardBucket_log_card
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ) (A L : ℝ≥0∞)
    (b : Fin (Nat.log 2 (Fintype.card ι) + 1)) {k : κ}
    (hk : k ∈ efficientLogCardBucket fine coarse active parent A L b) :
    Nat.log 2 ((rawIndexFactorization active parent).fiber k).card = b.1 := by
  have hlabel := (mem_dyadicFiber
    (efficientParents fine coarse active parent A L)
    (fiberLogCardLabel active parent) b k).1 hk |>.2
  exact congrArg Fin.val hlabel

omit [Fintype ι] in
/-- Every efficient parent is occupied, hence has a nonempty assigned fiber. -/
theorem efficientParent_fiber_nonempty
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ) (A L : ℝ≥0∞)
    {k : κ} (hk : k ∈ efficientParents fine coarse active parent A L) :
    ((rawIndexFactorization active parent).fiber k).Nonempty := by
  have hkOcc : k ∈ occupiedParents active parent :=
    (Finset.mem_filter.mp hk).1
  obtain ⟨i, hi, hiparent⟩ := Finset.mem_image.mp hkOcc
  exact ⟨i, (rawIndexFactorization active parent).mem_fiber i k |>.2
    ⟨hi, hiparent⟩⟩

/-- The common branching scale associated with a logarithmic bucket. -/
def logBucketBranching
    (b : Fin (Nat.log 2 (Fintype.card ι) + 1)) : ℕ :=
  2 ^ b.1

/-- With `B = 2^b`, every occupied fiber in bucket `b` satisfies
`B ≤ card < 2 * B`, and therefore also `card ≤ 2 * B`. -/
theorem efficientLogCardBucket_fiber_card_bounds
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ) (A L : ℝ≥0∞)
    (b : Fin (Nat.log 2 (Fintype.card ι) + 1)) {k : κ}
    (hk : k ∈ efficientLogCardBucket fine coarse active parent A L b) :
    logBucketBranching b ≤
        ((rawIndexFactorization active parent).fiber k).card ∧
      ((rawIndexFactorization active parent).fiber k).card <
        2 * logBucketBranching b := by
  let n := ((rawIndexFactorization active parent).fiber k).card
  have hkEff : k ∈ efficientParents fine coarse active parent A L :=
    (mem_dyadicFiber
      (efficientParents fine coarse active parent A L)
      (fiberLogCardLabel active parent) b k).1 hk |>.1
  have hn0 : n ≠ 0 := by
    exact Finset.card_ne_zero.mpr
      (efficientParent_fiber_nonempty fine coarse active parent A L hkEff)
  have hlog : Nat.log 2 n = b.1 := by
    simpa [n] using
      efficientLogCardBucket_log_card fine coarse active parent A L b hk
  constructor
  · unfold logBucketBranching
    rw [← hlog]
    exact Nat.pow_log_le_self 2 hn0
  · have hupper := Nat.lt_pow_succ_log_self Nat.one_lt_two n
    unfold logBucketBranching
    rw [hlog] at hupper
    simpa [pow_succ, Nat.mul_comm] using hupper

/-- Efficient-parent selection followed by logarithmic fiber-cardinality
bucketing retains body mass with loss `2 * (log₂(card ι) + 1)`. -/
theorem exists_efficientLogCardBucket_withinFactor
    (fine : UniformTubeFamily δ ι) (coarse : UniformTubeFamily ρ κ)
    (active : Finset ι) (parent : ι → κ) (A L : ℝ≥0∞)
    (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hcoverCost :
      A * (∑ k ∈ occupiedParents active parent,
        volume (coarse.tubes k).carrier) ≤
      L * bodyMassOn fine.bodyFamily active) :
    ∃ b : Fin (Nat.log 2 (Fintype.card ι) + 1),
      WithinFactor (2 * (Nat.log 2 (Fintype.card ι) + 1))
        (bodyMassOn fine.bodyFamily active)
        (∑ k ∈ efficientLogCardBucket fine coarse active parent A L b,
          assignedBodyMass fine active parent k) := by
  have hgood : WithinFactor 2 (bodyMassOn fine.bodyFamily active)
      (∑ k ∈ efficientParents fine coarse active parent A L,
        assignedBodyMass fine active parent k) := by
    unfold WithinFactor
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using
      bodyMass_le_two_mul_efficient_mass fine coarse active parent A L
        hL0 hLtop hcoverCost
  obtain ⟨b, hb⟩ := HeavyParentSelection.exists_parentLabel_weightedBucket
    (efficientParents fine coarse active parent A L)
    (fiberLogCardLabel active parent)
    (assignedBodyMass fine active parent)
  refine ⟨b, ?_⟩
  have hbucket :
      WithinFactor
        (Fintype.card (Fin (Nat.log 2 (Fintype.card ι) + 1)))
        (∑ k ∈ efficientParents fine coarse active parent A L,
          assignedBodyMass fine active parent k)
        (∑ k ∈ efficientLogCardBucket fine coarse active parent A L b,
          assignedBodyMass fine active parent k) := hb
  simpa [efficientLogCardBucket] using hgood.trans hbucket

end

end Submission.Kakeya.ConvexFactoring.JointTubeFactoring
