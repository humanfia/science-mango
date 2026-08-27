import ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit

/-!
# Exact-resonance support of broadened weak limits

Let a fixed finite measure be weighted by the normalized finite-time
resonance peak along observation times tending to infinity.  If those
weighted finite measures have a finite weak limit, then that limit is carried
by the exact zero set of the continuous mismatch.

The proof does not assume a density.  Near zero, the bounded defect is paid
for by its small size and the convergent total broadened mass.  Away from
zero, the explicit inverse-time sinc-squared bound makes the mass vanish.
This theorem identifies support of any future canonical on-shell cluster
point; it does not assert existence, uniqueness, or positivity of that
cluster point.
-/

open scoped Topology

namespace ArchonPhysics.BroadenedResonanceWeakLimitSupport

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.LocalCollisionDensityTransfer
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory Topology

noncomputable section

variable {X : Type*}

/-- A bounded continuous defect which vanishes exactly at zero mismatch. -/
def resonanceDefect (mismatch : X -> Real) (x : X) : Real :=
  min 1 |mismatch x|

theorem resonanceDefect_nonneg (mismatch : X -> Real) (x : X) :
    0 <= resonanceDefect mismatch x := by
  exact le_min zero_le_one (abs_nonneg _)

theorem resonanceDefect_le_one (mismatch : X -> Real) (x : X) :
    resonanceDefect mismatch x <= 1 :=
  min_le_left _ _

theorem resonanceDefect_le_abs (mismatch : X -> Real) (x : X) :
    resonanceDefect mismatch x <= |mismatch x| :=
  min_le_right _ _

theorem resonanceDefect_eq_zero_iff (mismatch : X -> Real) (x : X) :
    resonanceDefect mismatch x = 0 <-> mismatch x = 0 := by
  unfold resonanceDefect
  constructor
  · intro hzero
    have habs : |mismatch x| = 0 := by
      by_contra hne
      have hpos : 0 < |mismatch x| :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
      have : 0 < min 1 |mismatch x| := lt_min one_pos hpos
      linarith
    exact abs_eq_zero.mp habs
  · intro hzero
    simp [hzero]

section Topological

variable [TopologicalSpace X]

theorem continuous_resonanceDefect
    (mismatch : X -> Real) (hmismatch : Continuous mismatch) :
    Continuous (resonanceDefect mismatch) := by
  unfold resonanceDefect
  fun_prop

/-- Bundled bounded continuous exact-resonance defect. -/
def resonanceDefectBCF
    (mismatch : X -> Real) (hmismatch : Continuous mismatch) :
    BoundedContinuousFunction X Real :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (resonanceDefect mismatch)
    (continuous_resonanceDefect mismatch hmismatch)
    1
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (resonanceDefect_nonneg mismatch x)]
      exact resonanceDefect_le_one mismatch x)

@[simp]
theorem resonanceDefectBCF_apply
    (mismatch : X -> Real) (hmismatch : Continuous mismatch) (x : X) :
    resonanceDefectBCF mismatch hmismatch x = resonanceDefect mismatch x := by
  rfl

end Topological

/-- Pointwise near/far decomposition of the defect-weighted resonance peak. -/
theorem normalizedKernel_mul_resonanceDefect_le
    (mismatch : X -> Real) {T delta : Real}
    (hT : 0 < T) (hdelta : 0 < delta) (x : X) :
    normalizedFiniteTimeResonanceKernel (mismatch x) T *
        resonanceDefect mismatch x <=
      delta * normalizedFiniteTimeResonanceKernel (mismatch x) T +
        offGapCoefficient delta T := by
  have hkernel :
      0 <= normalizedFiniteTimeResonanceKernel (mismatch x) T :=
    normalizedFiniteTimeResonanceKernel_nonneg (mismatch x) T
  by_cases hnear : |mismatch x| < delta
  · have hdefect : resonanceDefect mismatch x <= delta :=
      (resonanceDefect_le_abs mismatch x).trans (le_of_lt hnear)
    calc
      normalizedFiniteTimeResonanceKernel (mismatch x) T *
          resonanceDefect mismatch x <=
        normalizedFiniteTimeResonanceKernel (mismatch x) T * delta :=
          mul_le_mul_of_nonneg_left hdefect hkernel
      _ = delta * normalizedFiniteTimeResonanceKernel (mismatch x) T := by
        ring
      _ <= delta * normalizedFiniteTimeResonanceKernel (mismatch x) T +
          offGapCoefficient delta T :=
        le_add_of_nonneg_right (offGapCoefficient_nonneg hdelta hT)
  · have hgap : delta <= |mismatch x| := le_of_not_gt hnear
    have hoff : normalizedFiniteTimeResonanceKernel (mismatch x) T <=
        offGapCoefficient delta T :=
      normalizedFiniteTimeResonanceKernel_le_offGapCoefficient
        hdelta hT hgap
    calc
      normalizedFiniteTimeResonanceKernel (mismatch x) T *
          resonanceDefect mismatch x <=
        normalizedFiniteTimeResonanceKernel (mismatch x) T * 1 :=
          mul_le_mul_of_nonneg_left
            (resonanceDefect_le_one mismatch x) hkernel
      _ = normalizedFiniteTimeResonanceKernel (mismatch x) T := by ring
      _ <= offGapCoefficient delta T := hoff
      _ <= delta * normalizedFiniteTimeResonanceKernel (mismatch x) T +
          offGapCoefficient delta T :=
        le_add_of_nonneg_left (mul_nonneg hdelta.le hkernel)

variable [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-- Integral form of the near/far decomposition. -/
theorem integral_resonanceDefect_broadened_le
    (mu : FiniteMeasure X) (mismatch : X -> Real)
    (hmismatch : Continuous mismatch) {T delta : Real}
    (hT : 0 < T) (hdelta : 0 < delta) :
    (∫ x, resonanceDefect mismatch x
      ∂(broadenedResonanceMeasure mu mismatch hmismatch.measurable T hT :
        Measure X)) <=
      delta *
          ((broadenedResonanceMeasure mu mismatch hmismatch.measurable T hT).mass :
            Real) +
        offGapCoefficient delta T * (mu.mass : Real) := by
  rw [integral_broadenedResonanceMeasure]
  simp only [smul_eq_mul]
  let kernelBCF := normalizedFiniteTimeResonanceWeightBCF
    mismatch hmismatch T hT
  let defectBCF := resonanceDefectBCF mismatch hmismatch
  have hleft : Integrable
      (fun x => normalizedFiniteTimeResonanceKernel (mismatch x) T *
        resonanceDefect mismatch x) (mu : Measure X) := by
    exact ((kernelBCF * defectBCF).integrable (mu : Measure X)).congr
      (Eventually.of_forall fun x => by rfl)
  have hkernel : Integrable
      (fun x => normalizedFiniteTimeResonanceKernel (mismatch x) T)
      (mu : Measure X) := by
    exact kernelBCF.integrable (mu : Measure X)
  have hright : Integrable
      (fun x => delta * normalizedFiniteTimeResonanceKernel (mismatch x) T +
        offGapCoefficient delta T) (mu : Measure X) :=
    (hkernel.const_mul delta).add (integrable_const _)
  calc
    (∫ x, normalizedFiniteTimeResonanceKernel (mismatch x) T *
        resonanceDefect mismatch x ∂(mu : Measure X)) <=
      ∫ x, delta * normalizedFiniteTimeResonanceKernel (mismatch x) T +
        offGapCoefficient delta T ∂(mu : Measure X) :=
      integral_mono hleft hright
        (fun x => normalizedKernel_mul_resonanceDefect_le
          mismatch hT hdelta x)
    _ = delta *
          ((broadenedResonanceMeasure mu mismatch hmismatch.measurable T hT).mass :
            Real) +
        offGapCoefficient delta T * (mu.mass : Real) := by
      rw [integral_add (hkernel.const_mul delta) (integrable_const _),
        integral_const_mul,
        broadenedResonanceMeasure_mass_eq_integral]
      simp [FiniteMeasure.mass, mul_comm]

/-- Every finite weak limit of fixed-measure broadenings along times tending
to infinity is concentrated on exact resonance. -/
theorem weakLimit_mismatch_eq_zero_ae
    (mu : FiniteMeasure X) (mismatch : X -> Real)
    (hmismatch : Continuous mismatch)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (target : FiniteMeasure X)
    (hweak : Tendsto
      (fun n => broadenedResonanceMeasure mu mismatch hmismatch.measurable
        (time n) (htime_pos n))
      atTop (nhds target)) :
    ∀ᵐ x ∂(target : Measure X), mismatch x = 0 := by
  let broadened : Nat -> FiniteMeasure X := fun n =>
    broadenedResonanceMeasure mu mismatch hmismatch.measurable
      (time n) (htime_pos n)
  have hmassNN : Tendsto (fun n => (broadened n).mass)
      atTop (nhds target.mass) := hweak.mass
  have hmass : Tendsto (fun n => ((broadened n).mass : Real))
      atTop (nhds (target.mass : Real)) :=
    (NNReal.continuous_coe.tendsto target.mass).comp hmassNN
  have hintegralWeak : Tendsto
      (fun n => ∫ x, resonanceDefect mismatch x
        ∂(broadened n : Measure X))
      atTop
      (nhds (∫ x, resonanceDefect mismatch x ∂(target : Measure X))) := by
    simpa only [broadened, resonanceDefectBCF_apply] using
      ((FiniteMeasure.tendsto_iff_forall_integral_tendsto).1 hweak
        (resonanceDefectBCF mismatch hmismatch))
  have hintegralZero : Tendsto
      (fun n => ∫ x, resonanceDefect mismatch x
        ∂(broadened n : Measure X))
      atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro epsilon hepsilon
    let M : Real := (target.mass : Real) + 1
    have hM : 0 < M := by
      dsimp [M]
      positivity
    let delta : Real := epsilon / (4 * M)
    have hdelta : 0 < delta := by
      dsimp [delta]
      positivity
    have hmassEventually : ∀ᶠ n in atTop, ((broadened n).mass : Real) < M :=
      hmass.eventually (Iio_mem_nhds (by dsimp [M]; linarith))
    have hoff : Tendsto
        (fun n => offGapCoefficient delta (time n) * (mu.mass : Real))
        atTop (nhds 0) := by
      have hdiv := htime.const_div_atTop ((2 / delta) ^ 2)
      have hscaled := hdiv.mul_const ((2 * Real.pi)⁻¹ * (mu.mass : Real))
      simpa [offGapCoefficient, div_eq_mul_inv, mul_assoc] using hscaled
    have hoffEventually : ∀ᶠ n in atTop,
        offGapCoefficient delta (time n) * (mu.mass : Real) < epsilon / 2 :=
      hoff.eventually (Iio_mem_nhds (half_pos hepsilon))
    filter_upwards [hmassEventually, hoffEventually] with n hmassN hoffN
    have hnonneg : 0 <= ∫ x, resonanceDefect mismatch x
        ∂(broadened n : Measure X) :=
      integral_nonneg (resonanceDefect_nonneg mismatch)
    have hbound := integral_resonanceDefect_broadened_le
      mu mismatch hmismatch (htime_pos n) hdelta
    change dist (∫ x, resonanceDefect mismatch x
      ∂(broadened n : Measure X)) 0 < epsilon
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    calc
      (∫ x, resonanceDefect mismatch x ∂(broadened n : Measure X)) <=
          delta * ((broadened n).mass : Real) +
            offGapCoefficient delta (time n) * (mu.mass : Real) := hbound
      _ < delta * M + epsilon / 2 := by
        exact add_lt_add
          (mul_lt_mul_of_pos_left hmassN hdelta) hoffN
      _ = 3 * epsilon / 4 := by
        dsimp [delta]
        field_simp [ne_of_gt hM]
        ring
      _ < epsilon := by linarith
  have htargetIntegral :
      (∫ x, resonanceDefect mismatch x ∂(target : Measure X)) = 0 :=
    tendsto_nhds_unique hintegralWeak hintegralZero
  have hdefectZero : resonanceDefect mismatch =ᵐ[(target : Measure X)] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (resonanceDefect_nonneg mismatch)
      ((resonanceDefectBCF mismatch hmismatch).integrable
        (target : Measure X))).mp htargetIntegral
  filter_upwards [hdefectZero] with x hx
  exact (resonanceDefect_eq_zero_iff mismatch x).mp hx

end

end ArchonPhysics.BroadenedResonanceWeakLimitSupport
