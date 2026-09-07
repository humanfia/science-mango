import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaConnectorV4

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentCertifiedPlankCordobaScaleFloorV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Family8CertifiedPlankPairOverlapV2
open Family8CertifiedPlankDyadicCordobaV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV4

noncomputable section

/-!
# A genuine container/floor bound for the canonical plank-angle scale

The V4 canonical factor contains the full body of row `i` in its exceptional
self-class.  Thus a finite bound necessarily forces a pointwise lower bound
for every shaded carrier; total shading mass alone cannot prove it.  This
file records that obstruction and proves the strongest direct scale producer:
a common convex container, a positive finite carrier floor, and the literal
finite maximum of the already constructed angle scales bound the complete
V4 double supremum.

No canonical-scale inequality is assumed below.  The row hull is the actual
V4 hull, and its volume bound is proved from body containment, including the
empty-angle-row case.
-/

universe u

variable {iota : Type u} [Fintype iota]
variable {F : ConvexFamily iota} {Y : Shading F}
variable {C a b : NNReal}

/-- Closed convex hull of every member of the certified family. -/
noncomputable def certifiedPlankFullHullContainer (F : ConvexFamily iota) :
    ConvexBody Space :=
  hullContainer F Finset.univ

theorem body_subset_certifiedPlankFullHullContainer
    (F : ConvexFamily iota) (i : iota) :
    (F i : Set Space) ⊆ (certifiedPlankFullHullContainer F : Set Space) := by
  classical
  exact body_subset_hullContainer F (Finset.mem_univ i)
    ⟨i, Finset.mem_univ i⟩

/-- Every V4 row hull has volume at most that of any common convex container.
For an empty row its canonical singleton hull has zero volume. -/
theorem volume_certifiedPlankDyadicHullContainer_le_globalContainer
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (K : ConvexBody Space)
    (hcontains : ∀ j, (F j : Set Space) ⊆ (K : Set Space))
    (i : iota) (k : Option Int) :
    volume (certifiedPlankDyadicHullContainer cert i k : Set Space) ≤
      volume (K : Set Space) := by
  classical
  by_cases hrow : (certifiedPlankDyadicRowIndices cert i k).Nonempty
  · exact measure_mono (hullContainer_subset F hrow (fun j _hj ↦ hcontains j))
  · have hempty : certifiedPlankDyadicRowIndices cert i k = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hrow
    simp [certifiedPlankDyadicHullContainer, hempty]

/-- Literal finite maximum of all angle scales appearing in V4. -/
noncomputable def canonicalCertifiedPlankAngleScaleCap
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i)) : ENNReal :=
  ⨆ k : {k // k ∈ plankAngleLevels (certifiedPlankDyadicLevels cert)},
    certifiedPlankAngleScale C a b
      certifiedPlankDyadicInverseSineWeight k.1

theorem certifiedPlankAngleScale_le_cap
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (k : Option Int)
    (hk : k ∈ plankAngleLevels (certifiedPlankDyadicLevels cert)) :
    certifiedPlankAngleScale C a b
        certifiedPlankDyadicInverseSineWeight k ≤
      canonicalCertifiedPlankAngleScaleCap cert := by
  exact le_iSup (fun l : {l // l ∈
    plankAngleLevels (certifiedPlankDyadicLevels cert)} ↦
      certifiedPlankAngleScale C a b
        certifiedPlankDyadicInverseSineWeight l.1) ⟨k, hk⟩

theorem canonicalCertifiedPlankAngleScaleCap_ne_top
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (hC : C ≠ 0) :
    canonicalCertifiedPlankAngleScaleCap cert ≠ ∞ := by
  apply iSup_ne_top
  intro k
  cases k.1 with
  | none => simp [certifiedPlankAngleScale]
  | some label =>
      simp only [certifiedPlankAngleScale,
        certifiedPlankDyadicInverseSineWeight]
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · exact ENNReal.ofReal_ne_top
          · norm_num
        · exact ENNReal.coe_ne_top
      · simp [hC]

/-- The complete V4 double supremum is bounded by the actual common-container
volume divided by the actual row-carrier floor, times the finite angle cap. -/
theorem canonicalCertifiedPlankAngleContainerScaleFactor_le_globalContainer
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (Y : Shading F) (K : ConvexBody Space)
    (hcontains : ∀ j, (F j : Set Space) ⊆ (K : Set Space))
    (lower : ENNReal) (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfloor : ∀ i, lower ≤ volume (Y.carrier i)) :
    canonicalCertifiedPlankAngleContainerScaleFactor cert Y ≤
      canonicalCertifiedPlankAngleScaleCap cert *
        (volume (K : Set Space) / lower) := by
  unfold canonicalCertifiedPlankAngleContainerScaleFactor
  apply iSup_le
  intro i
  apply iSup_le
  intro k
  have hcarrier0 : volume (Y.carrier i) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hlower0) (hfloor i))
  have hcarrierTop : volume (Y.carrier i) ≠ ∞ :=
    ((measure_mono (Y.carrier_subset i)).trans_lt
      (F i).isCompact.measure_lt_top).ne
  apply (ENNReal.div_le_iff hcarrier0 hcarrierTop).2
  calc
    certifiedPlankAngleScale C a b
          certifiedPlankDyadicInverseSineWeight k.1 *
        volume (certifiedPlankDyadicHullContainer cert i k.1 : Set Space) ≤
        canonicalCertifiedPlankAngleScaleCap cert *
          volume (K : Set Space) := by
      exact mul_le_mul
        (certifiedPlankAngleScale_le_cap cert k.1 k.2)
        (volume_certifiedPlankDyadicHullContainer_le_globalContainer
          cert K hcontains i k.1) bot_le bot_le
    _ = canonicalCertifiedPlankAngleScaleCap cert *
        ((volume (K : Set Space) / lower) * lower) := by
      rw [ENNReal.div_mul_cancel hlower0 hlowerTop]
    _ ≤ canonicalCertifiedPlankAngleScaleCap cert *
        ((volume (K : Set Space) / lower) * volume (Y.carrier i)) := by
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (hfloor i))
    _ = (canonicalCertifiedPlankAngleScaleCap cert *
        (volume (K : Set Space) / lower)) * volume (Y.carrier i) := by
      ring

/-- Full-family specialization: the common container is itself automatic. -/
theorem canonicalCertifiedPlankAngleContainerScaleFactor_le_fullHull
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (Y : Shading F)
    (lower : ENNReal) (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfloor : ∀ i, lower ≤ volume (Y.carrier i)) :
    canonicalCertifiedPlankAngleContainerScaleFactor cert Y ≤
      canonicalCertifiedPlankAngleScaleCap cert *
        (volume (certifiedPlankFullHullContainer F : Set Space) / lower) := by
  exact canonicalCertifiedPlankAngleContainerScaleFactor_le_globalContainer
    cert Y (certifiedPlankFullHullContainer F)
      (body_subset_certifiedPlankFullHullContainer F)
      lower hlower0 hlowerTop hfloor

/-- Formal necessity of row density: because `i` lies in its exceptional
self-row, any finite canonical cap controls the full body by its carrier. -/
theorem body_volume_le_of_canonicalCertifiedPlankAngleContainerScaleFactor_le
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (Y : Shading F) (A : ENNReal)
    (hscale : canonicalCertifiedPlankAngleContainerScaleFactor cert Y ≤ A)
    (hAfinite : A ≠ ∞) (i : iota) :
    volume (F i : Set Space) ≤ A * volume (Y.carrier i) := by
  have hi : i ∈ certifiedPlankDyadicRowIndices cert i none := by
    rw [mem_certifiedPlankDyadicRowIndices,
      certifiedPlankDyadicPairLevel_self]
  have hbody : (F i : Set Space) ⊆
      (certifiedPlankDyadicHullContainer cert i none : Set Space) :=
    body_subset_hullContainer F hi ⟨i, hi⟩
  have hnone : none ∈ plankAngleLevels (certifiedPlankDyadicLevels cert) := by
    simp [plankAngleLevels]
  have hrow := certifiedPlankAngleContainer_scale_le_of_canonical_le
    cert Y A hAfinite hscale i none hnone
  have hrow' :
      volume (certifiedPlankDyadicHullContainer cert i none : Set Space) ≤
        A * volume (Y.carrier i) := by
    simpa only [certifiedPlankAngleScale, one_mul] using hrow
  exact (measure_mono hbody).trans hrow'

#print axioms volume_certifiedPlankDyadicHullContainer_le_globalContainer
#print axioms canonicalCertifiedPlankAngleScaleCap_ne_top
#print axioms canonicalCertifiedPlankAngleContainerScaleFactor_le_globalContainer
#print axioms canonicalCertifiedPlankAngleContainerScaleFactor_le_fullHull

end
end Family8SelectedParentCertifiedPlankCordobaScaleFloorV5
