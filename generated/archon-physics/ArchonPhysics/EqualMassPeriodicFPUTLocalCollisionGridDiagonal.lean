import ArchonPhysics.EqualMassPeriodicFPUTNearResonantGridCertificate
import ArchonPhysics.FPUTFiniteTimeCollisionQuadrature
import ArchonPhysics.PeriodicFourierGridTensorResonanceChartDiagonal

/-!
# Local Fourier-grid diagonal limit for an Umklapp collision chart

This module inserts a positively oriented local Umklapp chart into the
periodic Fourier grid.  The local mark is extended by clamping to the chart
endpoints; when the mark vanishes at both endpoints, this is its continuous
zero extension.  Consequently the full periodic grid sum, with spacing
`2π/N`, is a genuine Riemann sum for the local chart integral.

The available deterministic Lipschitz estimate gives the transparent joint
window `T_N^2/N → 0`.  A separate certificate isolates the sharper bounded-
variation estimate that would reduce this to the physically optimal
`T_N/N → 0`.  No kinetic equation, RPA, or equidistribution assumption is
used.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTLocalCollisionGridDiagonal

open Set
open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTActualRootedEffectiveCoefficient
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalPositiveRootBrillouin
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalUmklappCompactTest
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTDirectSectorClosure
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate
open ArchonPhysics.EqualMassPeriodicFPUTNearResonantGridCertificate
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionChartAdapter
open ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionDensity
open ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality
open ArchonPhysics.FPUTFiniteTimeCollisionQuadrature
open ArchonPhysics.Lattice
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.PeriodicFourierGridQuadrature
open ArchonPhysics.PeriodicFourierGridTensorResonanceChartDiagonal
open ArchonPhysics.TransverseResonanceChartApproximateIdentity
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory Topology
open scoped BigOperators

noncomputable section

/-! ## Continuous zero extension of one local chart -/

/-- Clamp a local mark to a closed chart interval.  If its two endpoint
values vanish, this is exactly the continuous zero extension. -/
def clampedChartMark (a b : Real) (hab : a ≤ b)
    (mark : Real → Real) (x : Real) : Real :=
  mark (Set.projIcc a b hab x)

theorem clampedChartMark_eq_of_mem
    {a b : Real} (hab : a ≤ b) (mark : Real → Real)
    {x : Real} (hx : x ∈ Icc a b) :
    clampedChartMark a b hab mark x = mark x := by
  simp [clampedChartMark, Set.projIcc_of_mem hab hx]

theorem clampedChartMark_eq_zero_of_le_left
    {a b : Real} (hab : a ≤ b) {mark : Real → Real}
    (hmarkLeft : mark a = 0) {x : Real} (hx : x ≤ a) :
    clampedChartMark a b hab mark x = 0 := by
  simp [clampedChartMark, Set.projIcc_of_le_left hab hx, hmarkLeft]

theorem clampedChartMark_eq_zero_of_right_le
    {a b : Real} (hab : a ≤ b) {mark : Real → Real}
    (hmarkRight : mark b = 0) {x : Real} (hx : b ≤ x) :
    clampedChartMark a b hab mark x = 0 := by
  simp [clampedChartMark, Set.projIcc_of_right_le hab hx, hmarkRight]

theorem support_clampedChartMark_subset_Ioc
    {a b : Real} (hab : a ≤ b) {mark : Real → Real}
    (hmarkLeft : mark a = 0) (hmarkRight : mark b = 0) :
    Function.support (clampedChartMark a b hab mark) ⊆ Ioc a b := by
  intro x hx
  have hxa : a < x := by
    by_contra hnot
    exact hx (clampedChartMark_eq_zero_of_le_left
      hab hmarkLeft (le_of_not_gt hnot))
  have hxb : x < b := by
    by_contra hnot
    exact hx (clampedChartMark_eq_zero_of_right_le
      hab hmarkRight (le_of_not_gt hnot))
  exact ⟨hxa, hxb.le⟩

theorem continuous_clampedChartMark
    {a b : Real} (hab : a ≤ b) {mark : Real → Real}
    (hmark : Continuous mark) :
    Continuous (clampedChartMark a b hab mark) := by
  exact hmark.comp (continuous_subtype_val.comp continuous_projIcc)

theorem abs_clampedChartMark_sub_le
    {a b markSlope : Real} (hab : a ≤ b) (hmarkSlope : 0 ≤ markSlope)
    {mark : Real → Real}
    (hmarkLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |mark x - mark y| ≤ markSlope * |x - y|)
    (x y : Real) :
    |clampedChartMark a b hab mark x -
        clampedChartMark a b hab mark y| ≤
      markSlope * |x - y| := by
  have hlocal := hmarkLip
    (Set.projIcc a b hab x) (Set.projIcc a b hab x).property
    (Set.projIcc a b hab y) (Set.projIcc a b hab y).property
  have hprojection := (LipschitzWith.projIcc hab).dist_le_mul x y
  have hprojection' :
      |((Set.projIcc a b hab x : Icc a b) : Real) -
          ((Set.projIcc a b hab y : Icc a b) : Real)| ≤ |x - y| := by
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq] using
      hprojection
  unfold clampedChartMark
  exact hlocal.trans
    (mul_le_mul_of_nonneg_left hprojection' hmarkSlope)

theorem abs_clampedChartMark_le
    {a b markBound : Real} (hab : a ≤ b) {mark : Real → Real}
    (hmarkBound : ∀ x ∈ Icc a b, |mark x| ≤ markBound)
    (x : Real) :
    |clampedChartMark a b hab mark x| ≤ markBound :=
  hmarkBound (Set.projIcc a b hab x) (Set.projIcc a b hab x).property

theorem intervalIntegral_clampedCollision_eq_local
    {a b : Real} (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hb2pi : b ≤ 2 * Real.pi)
    {mismatch mark : Real → Real} {T : Real}
    (hmarkLeft : mark a = 0) (hmarkRight : mark b = 0) :
    (∫ x in (0 : Real)..(2 * Real.pi),
        finiteTimeMarkedCollisionIntegrand mismatch
          (clampedChartMark a b hab mark) T x) =
      ∫ x in a..b,
        finiteTimeMarkedCollisionIntegrand mismatch mark T x := by
  let clampedIntegrand : Real → Real := fun x ↦
    finiteTimeMarkedCollisionIntegrand mismatch
      (clampedChartMark a b hab mark) T x
  have hsupportLocal : Function.support clampedIntegrand ⊆ Ioc a b := by
    exact (Function.support_mul_subset_left
      (clampedChartMark a b hab mark)
      (fun x ↦ normalizedFiniteTimeResonanceKernel (mismatch x) T)).trans
        (support_clampedChartMark_subset_Ioc hab hmarkLeft hmarkRight)
  have hsupportFull : Function.support clampedIntegrand ⊆
      Ioc (0 : Real) (2 * Real.pi) := by
    intro x hx
    have hxab := hsupportLocal hx
    exact ⟨ha0.trans_lt hxab.1, hxab.2.trans hb2pi⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsupportFull]
  calc
    (∫ x : Real, clampedIntegrand x) =
        ∫ x in a..b, clampedIntegrand x :=
      (intervalIntegral.integral_eq_integral_of_support_subset
        hsupportLocal).symm
    _ = ∫ x in a..b,
        finiteTimeMarkedCollisionIntegrand mismatch mark T x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hab] at hx
      simp only [clampedIntegrand, finiteTimeMarkedCollisionIntegrand,
        clampedChartMark_eq_of_mem hab mark hx]

/-! ## Correctly normalized local Fourier-grid sum -/

/-- The local collision Riemann sum.  The prefactor is the physical Fourier
spacing `2π/N`; the time normalization is already contained in the normalized
finite-time resonance kernel. -/
def localFourierGridCollisionQuadrature
    (N : Nat) [NeZero N] (mismatch mark : Real → Real)
    (a b : Real) (hab : a ≤ b) (T : Real) : Real :=
  (2 * Real.pi / (N : Real)) *
    ∑ mode : Site N,
      finiteTimeMarkedCollisionIntegrand mismatch
        (clampedChartMark a b hab mark) T (gridWaveNumber N mode)

theorem abs_localFourierGridCollisionQuadrature_sub_integral_le
    (N : Nat) [NeZero N]
    {mismatch mark : Real → Real} {a b T : Real}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb2pi : b ≤ 2 * Real.pi)
    {markBound markSlope mismatchSlope : Real}
    (hT : 0 < T) (hmarkBound : 0 ≤ markBound)
    (hmarkSlope : 0 ≤ markSlope) (hmismatchSlope : 0 ≤ mismatchSlope)
    (hmarkContinuous : Continuous mark)
    (hmismatchContinuous : Continuous mismatch)
    (hmarkLeft : mark a = 0) (hmarkRight : mark b = 0)
    (hmarkBoundOn : ∀ x ∈ Icc a b, |mark x| ≤ markBound)
    (hmarkLipOn : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |mark x - mark y| ≤ markSlope * |x - y|)
    (hmismatchLipOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
        |mismatch x - mismatch y| ≤ mismatchSlope * |x - y|) :
    |localFourierGridCollisionQuadrature N mismatch mark a b hab T -
      ∫ x in a..b,
        finiteTimeMarkedCollisionIntegrand mismatch mark T x| ≤
      finiteTimeMarkedCollisionLipschitzConstant
          T markBound markSlope mismatchSlope *
        (2 * Real.pi) ^ 2 / (N : Real) := by
  rw [← intervalIntegral_clampedCollision_eq_local
    hab ha0 hb2pi hmarkLeft hmarkRight]
  unfold localFourierGridCollisionQuadrature
  apply abs_fourierGrid_sum_sub_integral_le_of_lipschitz
  · exact finiteTimeMarkedCollisionLipschitzConstant_nonneg
      hT.le hmarkBound hmarkSlope hmismatchSlope
  · simp [finiteTimeMarkedCollisionIntegrand,
      clampedChartMark_eq_zero_of_le_left hab hmarkLeft ha0,
      clampedChartMark_eq_zero_of_right_le hab hmarkRight hb2pi]
  · exact (continuous_clampedChartMark hab hmarkContinuous).mul
      ((continuous_normalizedFiniteTimeResonanceKernel hT).comp
        hmismatchContinuous) |>.continuousOn
  · intro x hx y hy
    exact abs_finiteTimeMarkedCollisionIntegrand_sub_le
      hT hmarkBound hmarkSlope hmismatchSlope
      (abs_clampedChartMark_le hab hmarkBoundOn y)
      (abs_clampedChartMark_sub_le hab hmarkSlope hmarkLipOn x y)
      (hmismatchLipOn x hx y hy)

/-! ## Diagonal limits -/

/-- A local transverse chart plus a vanishing deterministic quadrature error
gives the full discrete Fourier-grid collision limit. -/
theorem localFourierGridCollisionQuadrature_tendsto_density_zero_of_scale
    {mismatch mismatchDerivative mark density : Real → Real}
    {a b : Real}
    (chart : TransverseResonanceChart
      mismatch mismatchDerivative mark density a b)
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb2pi : b ≤ 2 * Real.pi)
    {markBound markSlope mismatchSlope : Real}
    (hmarkBound : 0 ≤ markBound) (hmarkSlope : 0 ≤ markSlope)
    (hmismatchSlope : 0 ≤ mismatchSlope)
    (hmarkContinuous : Continuous mark)
    (hmismatchContinuous : Continuous mismatch)
    (hmarkLeft : mark a = 0) (hmarkRight : mark b = 0)
    (hmarkBoundOn : ∀ x ∈ Icc a b, |mark x| ≤ markBound)
    (hmarkLipOn : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |mark x - mark y| ≤ markSlope * |x - y|)
    (hmismatchLipOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
        |mismatch x - mismatch y| ≤ mismatchSlope * |x - y|)
    (time : Nat → Real) (htimePos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (hscale : Tendsto
      (fun n : Nat ↦
        finiteTimeMarkedCollisionLipschitzConstant
            (time n) markBound markSlope mismatchSlope *
          (2 * Real.pi) ^ 2 / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        localFourierGridCollisionQuadrature (n + 1)
          mismatch mark a b hab (time n))
      atTop (nhds (density 0)) := by
  let error : Nat → Real := fun n ↦
    finiteTimeMarkedCollisionLipschitzConstant
        (time n) markBound markSlope mismatchSlope *
      (2 * Real.pi) ^ 2 / (((n + 1 : Nat) : Real))
  apply discreteCollisionObservable_tendsto_density_zero_of_chart_error
    chart time
      (fun n ↦ localFourierGridCollisionQuadrature (n + 1)
        mismatch mark a b hab (time n)) error htime
  · intro n
    have hbound := abs_localFourierGridCollisionQuadrature_sub_integral_le
      (n + 1) hab ha0 hb2pi (htimePos n)
      hmarkBound hmarkSlope hmismatchSlope hmarkContinuous
      hmismatchContinuous hmarkLeft hmarkRight hmarkBoundOn
      hmarkLipOn hmismatchLipOn
    simpa only [error, transverseChartCollisionObservable,
      finiteTimeMarkedCollisionIntegrand, mul_comm] using hbound
  · exact hscale

/-- The current Lipschitz route closes under separate linear and quadratic
time/volume windows.  The quadratic window is the genuinely stronger input. -/
theorem localFourierGridCollisionQuadrature_tendsto_density_zero_of_time_sq
    {mismatch mismatchDerivative mark density : Real → Real}
    {a b : Real}
    (chart : TransverseResonanceChart
      mismatch mismatchDerivative mark density a b)
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb2pi : b ≤ 2 * Real.pi)
    {markBound markSlope mismatchSlope : Real}
    (hmarkBound : 0 ≤ markBound) (hmarkSlope : 0 ≤ markSlope)
    (hmismatchSlope : 0 ≤ mismatchSlope)
    (hmarkContinuous : Continuous mark)
    (hmismatchContinuous : Continuous mismatch)
    (hmarkLeft : mark a = 0) (hmarkRight : mark b = 0)
    (hmarkBoundOn : ∀ x ∈ Icc a b, |mark x| ≤ markBound)
    (hmarkLipOn : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |mark x - mark y| ≤ markSlope * |x - y|)
    (hmismatchLipOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
        |mismatch x - mismatch y| ≤ mismatchSlope * |x - y|)
    (time : Nat → Real) (htimePos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (hlinear : Tendsto
      (fun n : Nat ↦ time n / (((n + 1 : Nat) : Real)))
      atTop (nhds 0))
    (hquadratic : Tendsto
      (fun n : Nat ↦ (time n) ^ 2 / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        localFourierGridCollisionQuadrature (n + 1)
          mismatch mark a b hab (time n))
      atTop (nhds (density 0)) := by
  apply localFourierGridCollisionQuadrature_tendsto_density_zero_of_scale
    chart hab ha0 hb2pi hmarkBound hmarkSlope hmismatchSlope
      hmarkContinuous hmismatchContinuous hmarkLeft hmarkRight
      hmarkBoundOn hmarkLipOn hmismatchLipOn time htimePos htime
  let linearConstant : Real :=
    markSlope / (2 * Real.pi) * (2 * Real.pi) ^ 2
  let quadraticConstant : Real :=
    markBound / Real.pi * mismatchSlope * (2 * Real.pi) ^ 2
  have hlinearScaled : Tendsto
      (fun n : Nat ↦ linearConstant *
        (time n / (((n + 1 : Nat) : Real))))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlinear
  have hquadraticScaled : Tendsto
      (fun n : Nat ↦ quadraticConstant *
        ((time n) ^ 2 / (((n + 1 : Nat) : Real))))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hquadratic
  have heq :
      (fun n : Nat ↦
        finiteTimeMarkedCollisionLipschitzConstant
            (time n) markBound markSlope mismatchSlope *
          (2 * Real.pi) ^ 2 / (((n + 1 : Nat) : Real))) =
      (fun n : Nat ↦
        linearConstant * (time n / (((n + 1 : Nat) : Real))) +
          quadraticConstant *
            ((time n) ^ 2 / (((n + 1 : Nat) : Real)))) := by
    funext n
    dsimp [linearConstant, quadraticConstant,
      finiteTimeMarkedCollisionLipschitzConstant]
    ring
  rw [heq]
  simpa using hlinearScaled.add hquadraticScaled

/-! ## Isolating the optimal `T/N` input -/

/-- The one missing analytic input for the optimal diagonal window: a
bounded-variation quadrature estimate whose cost grows only linearly in
time.  It contains no kinetic or probabilistic assertion. -/
structure LinearTimeLocalCollisionQuadratureCertificate
    (mismatch mark : Real → Real) (a b : Real) (hab : a ≤ b) where
  constant : Real
  constant_nonneg : 0 ≤ constant
  error_bound : ∀ (N : Nat) [NeZero N] {T : Real}, 0 < T →
    |localFourierGridCollisionQuadrature N mismatch mark a b hab T -
      ∫ x in a..b,
        finiteTimeMarkedCollisionIntegrand mismatch mark T x| ≤
      constant * (1 + T) / (N : Real)

/-- Once the linear-time bounded-variation certificate is supplied, the
optimal joint window `T_N/N → 0` is sufficient. -/
theorem localFourierGridCollisionQuadrature_tendsto_density_zero_of_linearTime
    {mismatch mismatchDerivative mark density : Real → Real}
    {a b : Real}
    (chart : TransverseResonanceChart
      mismatch mismatchDerivative mark density a b)
    (hab : a ≤ b)
    (certificate : LinearTimeLocalCollisionQuadratureCertificate
      mismatch mark a b hab)
    (time : Nat → Real) (htimePos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (hlinear : Tendsto
      (fun n : Nat ↦ time n / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        localFourierGridCollisionQuadrature (n + 1)
          mismatch mark a b hab (time n))
      atTop (nhds (density 0)) := by
  let error : Nat → Real := fun n ↦
    certificate.constant * (1 + time n) /
      (((n + 1 : Nat) : Real))
  apply discreteCollisionObservable_tendsto_density_zero_of_chart_error
    chart time
      (fun n ↦ localFourierGridCollisionQuadrature (n + 1)
        mismatch mark a b hab (time n)) error htime
  · intro n
    have hbound := certificate.error_bound (n + 1) (htimePos n)
    simpa only [error, transverseChartCollisionObservable,
      finiteTimeMarkedCollisionIntegrand, mul_comm] using hbound
  · have hinverse : Tendsto
        (fun n : Nat ↦ (1 : Real) / (((n + 1 : Nat) : Real)))
        atTop (nhds 0) := by
      have hbase : Tendsto
          (fun n : Nat ↦ (((n + 1 : Nat) : Real))⁻¹)
          atTop (nhds 0) := by
        refine ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := Real)).comp
          (tendsto_add_atTop_nat 1)).congr' ?_
        exact Eventually.of_forall fun _ ↦ rfl
      simpa only [one_div] using hbase
    have hsum : Tendsto
        (fun n : Nat ↦
          1 / (((n + 1 : Nat) : Real)) +
            time n / (((n + 1 : Nat) : Real)))
        atTop (nhds 0) := by
      simpa using hinverse.add hlinear
    have hscaled : Tendsto
        (fun n : Nat ↦ certificate.constant *
          (1 / (((n + 1 : Nat) : Real)) +
            time n / (((n + 1 : Nat) : Real))))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hsum : Tendsto
        (fun n : Nat ↦ certificate.constant *
          (1 / (((n + 1 : Nat) : Real)) +
            time n / (((n + 1 : Nat) : Real))))
        atTop (nhds (certificate.constant * 0)))
    have heq : error = fun n : Nat ↦ certificate.constant *
        (1 / (((n + 1 : Nat) : Real)) +
          time n / (((n + 1 : Nat) : Real))) := by
      funext n
      dsimp [error]
      ring
    rw [heq]
    exact hscaled

/-! ## Actual rooted coefficient and explicit tent mark -/

def canonicalDiagramLocalLeft
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) : Real :=
  umklappArcsineLocalLeft
    (umklappPositiveArcsineBranch
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
    (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)

def canonicalDiagramLocalRight
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) : Real :=
  umklappArcsineLocalRight
    (umklappPositiveArcsineBranch
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
    (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)

def canonicalDiagramUmklappMismatch
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) (z : Real) : Real :=
  umklappReducedFourWaveMismatch
    (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram) z

/-- Finite deterministic regularity data for the actual rooted tent mark.
The construction theorem below generates this bundle from the explicit
Umklapp geometry; it is not an additional physical assumption. -/
structure ActualRootedLocalMarkRegularity
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) where
  markBound : Real
  markSlope : Real
  markBound_nonneg : 0 ≤ markBound
  markSlope_nonneg : 0 ≤ markSlope
  mark_left_zero :
    actualRootedLocalCollisionMark alpha out diagram
      (canonicalDiagramLocalLeft diagram) = 0
  mark_right_zero :
    actualRootedLocalCollisionMark alpha out diagram
      (canonicalDiagramLocalRight diagram) = 0
  mark_bound : ∀ z ∈ Icc
      (canonicalDiagramLocalLeft diagram)
      (canonicalDiagramLocalRight diagram),
    |actualRootedLocalCollisionMark alpha out diagram z| ≤ markBound
  mark_lipschitz : ∀ z ∈ Icc
      (canonicalDiagramLocalLeft diagram)
      (canonicalDiagramLocalRight diagram),
    ∀ w ∈ Icc
      (canonicalDiagramLocalLeft diagram)
      (canonicalDiagramLocalRight diagram),
      |actualRootedLocalCollisionMark alpha out diagram z -
        actualRootedLocalCollisionMark alpha out diagram w| ≤
          markSlope * |z - w|

theorem continuous_canonicalDiagramUmklappMismatch
    {N : Nat} [NeZero N] {out : ActualInteractionBranchMode N}
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) :
    Continuous (canonicalDiagramUmklappMismatch diagram) := by
  have hdiff : Differentiable Real
      (canonicalDiagramUmklappMismatch diagram) := fun z ↦
    (hasDerivAt_umklappReducedFourWaveMismatch_k₂_factor
      (canonicalDiagramGridK₀ diagram)
      (canonicalDiagramGridK₁ diagram) z).differentiableAt
  exact hdiff.continuous

theorem continuous_actualRootedLocalCollisionMark
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) :
    Continuous (actualRootedLocalCollisionMark alpha out diagram) := by
  have hdensity :=
    (actualRootedLocalCollisionDensity_data alpha out diagram hdisc).density_continuous
  have hmismatch := continuous_canonicalDiagramUmklappMismatch diagram
  have hderivative : Continuous (fun z : Real ↦
      umklappK₂DerivativeFactor
        (canonicalDiagramGridK₀ diagram)
        (canonicalDiagramGridK₁ diagram) z) := by
    unfold umklappK₂DerivativeFactor
    fun_prop
  change Continuous (fun z : Real ↦
    actualRootedLocalCollisionDensity alpha out diagram
        (canonicalDiagramUmklappMismatch diagram z) *
      umklappK₂DerivativeFactor
        (canonicalDiagramGridK₀ diagram)
        (canonicalDiagramGridK₁ diagram) z)
  exact (hdensity.comp hmismatch).mul hderivative

/-- The explicit tent mark is `C¹` relative to its selected closed chart.
The outer `max` disappears there because strict monotonicity puts the
mismatch between its two endpoint values. -/
theorem contDiffOn_actualRootedLocalCollisionMark
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) :
    ContDiffOn Real 1 (actualRootedLocalCollisionMark alpha out diagram)
      (Icc (canonicalDiagramLocalLeft diagram)
        (canonicalDiagramLocalRight diagram)) := by
  let k₀ := canonicalDiagramGridK₀ diagram
  let k₁ := canonicalDiagramGridK₁ diagram
  let a := canonicalDiagramLocalLeft diagram
  let b := canonicalDiagramLocalRight diagram
  let mismatch : Real → Real := canonicalDiagramUmklappMismatch diagram
  let coefficient : Real := Complex.normSq
    (reachableActualSwappedEffectiveFourWaveCoefficient N alpha out diagram)
  let smoothMark : Real → Real := fun z ↦
    coefficient *
      ((mismatch z - mismatch a) * (mismatch b - mismatch z)) *
        umklappK₂DerivativeFactor k₀ k₁ z
  let geometry := canonicalPositiveGeometry_principalZone
    (canonicalDiagramGridK₀_pos diagram)
    (canonicalDiagramGridK₀_lt_two_pi diagram)
    (canonicalDiagramGridK₁_pos diagram)
    (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc
  have hab : a ≤ b := by
    exact geometry.interval_lt.le
  have hsmooth : ContDiff Real 1 smoothMark := by
    dsimp [smoothMark, mismatch, coefficient,
      canonicalDiagramUmklappMismatch, k₀, k₁]
    unfold umklappReducedFourWaveMismatch continuumAcousticFrequency
      umklappK₂DerivativeFactor
    fun_prop
  apply hsmooth.contDiffOn.congr
  intro z hz
  have haMem : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hbMem : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hleft : mismatch a ≤ mismatch z :=
    geometry.mismatch_strictMono.monotoneOn haMem hz hz.1
  have hright : mismatch z ≤ mismatch b :=
    geometry.mismatch_strictMono.monotoneOn hz hbMem hz.2
  have hproduct :
      0 ≤ (mismatch z - mismatch a) * (mismatch b - mismatch z) :=
    mul_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr hright)
  have hproduct' :
      0 ≤
        (canonicalDiagramUmklappMismatch diagram z -
            canonicalDiagramUmklappMismatch diagram
              (canonicalDiagramLocalLeft diagram)) *
          (canonicalDiagramUmklappMismatch diagram
              (canonicalDiagramLocalRight diagram) -
            canonicalDiagramUmklappMismatch diagram z) := by
    simpa [mismatch, a, b] using hproduct
  dsimp [smoothMark, coefficient, mismatch, a, b, k₀, k₁]
  unfold actualRootedLocalCollisionMark umklappDensityInducedMark
    actualRootedLocalCollisionDensity canonicalPositiveUmklappTentDensity
    compactIntervalTentDensity canonicalDiagramLocalLeft
    canonicalDiagramLocalRight canonicalDiagramUmklappMismatch
  rw [max_eq_right (by
    simpa [canonicalDiagramUmklappMismatch, canonicalDiagramLocalLeft,
      canonicalDiagramLocalRight] using hproduct')]

/-- Compactness of the explicit chart turns the relative `C¹` result into
finite bound and slope constants. -/
theorem exists_actualRootedLocalMarkRegularity
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) :
    Nonempty (ActualRootedLocalMarkRegularity alpha out diagram) := by
  let a := canonicalDiagramLocalLeft diagram
  let b := canonicalDiagramLocalRight diagram
  let mark := actualRootedLocalCollisionMark alpha out diagram
  let geometry := canonicalPositiveGeometry_principalZone
    (canonicalDiagramGridK₀_pos diagram)
    (canonicalDiagramGridK₀_lt_two_pi diagram)
    (canonicalDiagramGridK₁_pos diagram)
    (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc
  have hab : a ≤ b := geometry.interval_lt.le
  have hcontdiff : ContDiffOn Real 1 mark (Icc a b) := by
    exact contDiffOn_actualRootedLocalCollisionMark alpha out diagram hdisc
  obtain ⟨K, hK⟩ := hcontdiff.exists_lipschitzOnWith
    (by norm_num) (convex_Icc a b) isCompact_Icc
  have hleft : mark a = 0 := by
    simp [mark, a, actualRootedLocalCollisionMark,
      umklappDensityInducedMark, actualRootedLocalCollisionDensity,
      canonicalPositiveUmklappTentDensity, compactIntervalTentDensity,
      canonicalDiagramLocalLeft]
  have hright : mark b = 0 := by
    simp [mark, b, actualRootedLocalCollisionMark,
      umklappDensityInducedMark, actualRootedLocalCollisionDensity,
      canonicalPositiveUmklappTentDensity, compactIntervalTentDensity,
      canonicalDiagramLocalRight]
  let slope : Real := K
  let bound : Real := slope * (b - a)
  have hslope : 0 ≤ slope := by positivity
  have hbound : 0 ≤ bound := mul_nonneg hslope (sub_nonneg.mpr hab)
  refine ⟨{
    markBound := bound
    markSlope := slope
    markBound_nonneg := hbound
    markSlope_nonneg := hslope
    mark_left_zero := ?_
    mark_right_zero := ?_
    mark_bound := ?_
    mark_lipschitz := ?_ }⟩
  · exact hleft
  · exact hright
  · intro z hz
    have hlip := hK.dist_le_mul z hz a (left_mem_Icc.mpr hab)
    rw [Real.dist_eq, Real.dist_eq, hleft, sub_zero] at hlip
    calc
      |mark z| ≤ slope * |z - a| := by simpa [slope] using hlip
      _ ≤ slope * (b - a) := by
        apply mul_le_mul_of_nonneg_left _ hslope
        rw [abs_of_nonneg (sub_nonneg.mpr hz.1)]
        linarith [hz.2]
      _ = bound := rfl
  · intro z hz w hw
    have hlip := hK.dist_le_mul z hz w hw
    simpa only [mark, slope, Real.dist_eq] using hlip

noncomputable def actualRootedLocalMarkRegularity
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) :
    ActualRootedLocalMarkRegularity alpha out diagram :=
  Classical.choice
    (exists_actualRootedLocalMarkRegularity alpha out diagram hdisc)

/-- Fully instantiated local thermodynamic bridge for the actual rooted
coefficient and explicit tent mark.  The chart endpoint inclusion in the
principal Brillouin interval remains explicit; the mark regularity constants
are constructed above. -/
theorem actualRootedLocalFourierGridCollision_tendsto_rate_of_time_sq
    {N₀ : Nat} [NeZero N₀] (alpha : Real)
    (out : ActualInteractionBranchMode N₀)
    (diagram : ActiveFeedbackEffectiveDiagramImage N₀ out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
    (ha0 : 0 ≤ canonicalDiagramLocalLeft diagram)
    (hb2pi : canonicalDiagramLocalRight diagram ≤ 2 * Real.pi)
    (time : Nat → Real) (htimePos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (hlinear : Tendsto
      (fun n : Nat ↦ time n / (((n + 1 : Nat) : Real)))
      atTop (nhds 0))
    (hquadratic : Tendsto
      (fun n : Nat ↦ (time n) ^ 2 / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        localFourierGridCollisionQuadrature (n + 1)
          (fun z ↦ umklappReducedFourWaveMismatch
            (canonicalDiagramGridK₀ diagram)
            (canonicalDiagramGridK₁ diagram) z)
          (umklappDensityInducedMark
            (canonicalDiagramGridK₀ diagram)
            (canonicalDiagramGridK₁ diagram)
            (actualRootedLocalCollisionDensity alpha out diagram))
          (umklappArcsineLocalLeft
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram)
              (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram)
            (canonicalDiagramGridK₁ diagram))
          (umklappArcsineLocalRight
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram)
              (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram)
            (canonicalDiagramGridK₁ diagram))
          (canonicalPositiveGeometry_principalZone
            (canonicalDiagramGridK₀_pos diagram)
            (canonicalDiagramGridK₀_lt_two_pi diagram)
            (canonicalDiagramGridK₁_pos diagram)
            (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc).interval_lt.le
          (time n))
      atTop (nhds (actualRootedLocalCollisionRate alpha out diagram)) := by
  let geometry := canonicalPositiveGeometry_principalZone
    (canonicalDiagramGridK₀_pos diagram)
    (canonicalDiagramGridK₀_lt_two_pi diagram)
    (canonicalDiagramGridK₁_pos diagram)
    (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc
  let densityData :=
    actualRootedLocalCollisionDensity_data alpha out diagram hdisc
  let measureData := densityData.toCollisionMeasureData
  let chart := measureData.toPositiveUmklappCollisionChart geometry
  let regularity := actualRootedLocalMarkRegularity alpha out diagram hdisc
  have hmismatchLip : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
        |canonicalDiagramUmklappMismatch diagram x -
          canonicalDiagramUmklappMismatch diagram y| ≤ 2 * |x - y| := by
    intro x _hx y _hy
    exact abs_umklappReducedFourWaveMismatch_sub_le
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram) x y
  have hlimit :=
    localFourierGridCollisionQuadrature_tendsto_density_zero_of_time_sq
      chart.toTransverseResonanceChart geometry.interval_lt.le ha0 hb2pi
      regularity.markBound_nonneg regularity.markSlope_nonneg
      (by norm_num : (0 : Real) ≤ 2)
      (continuous_actualRootedLocalCollisionMark alpha out diagram hdisc)
      (continuous_canonicalDiagramUmklappMismatch diagram)
      regularity.mark_left_zero regularity.mark_right_zero
      regularity.mark_bound regularity.mark_lipschitz hmismatchLip
      time htimePos htime hlinear hquadratic
  simpa only [actualRootedLocalCollisionRate] using hlimit

/-- Optimal-window endpoint for the same actual coefficient and tent mark.
The only extra object is the explicit `O(T/N)` bounded-variation quadrature
certificate isolated above. -/
theorem actualRootedLocalFourierGridCollision_tendsto_rate_of_linearTime
    {N₀ : Nat} [NeZero N₀] (alpha : Real)
    (out : ActualInteractionBranchMode N₀)
    (diagram : ActiveFeedbackEffectiveDiagramImage N₀ out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
    (certificate : LinearTimeLocalCollisionQuadratureCertificate
      (fun z ↦ umklappReducedFourWaveMismatch
        (canonicalDiagramGridK₀ diagram)
        (canonicalDiagramGridK₁ diagram) z)
      (umklappDensityInducedMark
        (canonicalDiagramGridK₀ diagram)
        (canonicalDiagramGridK₁ diagram)
        (actualRootedLocalCollisionDensity alpha out diagram))
      (umklappArcsineLocalLeft
        (umklappPositiveArcsineBranch
          (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
        (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
      (umklappArcsineLocalRight
        (umklappPositiveArcsineBranch
          (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
        (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
      (canonicalPositiveGeometry_principalZone
        (canonicalDiagramGridK₀_pos diagram)
        (canonicalDiagramGridK₀_lt_two_pi diagram)
        (canonicalDiagramGridK₁_pos diagram)
        (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc).interval_lt.le)
    (time : Nat → Real) (htimePos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (hlinear : Tendsto
      (fun n : Nat ↦ time n / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        localFourierGridCollisionQuadrature (n + 1)
          (fun z ↦ umklappReducedFourWaveMismatch
            (canonicalDiagramGridK₀ diagram)
            (canonicalDiagramGridK₁ diagram) z)
          (umklappDensityInducedMark
            (canonicalDiagramGridK₀ diagram)
            (canonicalDiagramGridK₁ diagram)
            (actualRootedLocalCollisionDensity alpha out diagram))
          (umklappArcsineLocalLeft
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram)
              (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram)
            (canonicalDiagramGridK₁ diagram))
          (umklappArcsineLocalRight
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram)
              (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram)
            (canonicalDiagramGridK₁ diagram))
          (canonicalPositiveGeometry_principalZone
            (canonicalDiagramGridK₀_pos diagram)
            (canonicalDiagramGridK₀_lt_two_pi diagram)
            (canonicalDiagramGridK₁_pos diagram)
            (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc).interval_lt.le
          (time n))
      atTop (nhds (actualRootedLocalCollisionRate alpha out diagram)) := by
  let geometry := canonicalPositiveGeometry_principalZone
    (canonicalDiagramGridK₀_pos diagram)
    (canonicalDiagramGridK₀_lt_two_pi diagram)
    (canonicalDiagramGridK₁_pos diagram)
    (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc
  let densityData :=
    actualRootedLocalCollisionDensity_data alpha out diagram hdisc
  let measureData := densityData.toCollisionMeasureData
  let chart := measureData.toPositiveUmklappCollisionChart geometry
  have hlimit :=
    localFourierGridCollisionQuadrature_tendsto_density_zero_of_linearTime
      chart.toTransverseResonanceChart geometry.interval_lt.le certificate
      time htimePos htime hlinear
  simpa only [actualRootedLocalCollisionRate] using hlimit

/-- The limiting actual rate in either diagonal theorem is strictly positive
as soon as the physical cubic coupling is nonzero. -/
theorem actualRootedLocalFourierGridCollision_rate_pos
    {N : Nat} [NeZero N] {alpha : Real} (halpha : alpha ≠ 0)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) :
    0 < actualRootedLocalCollisionRate alpha out diagram :=
  actualRootedLocalCollisionRate_pos halpha out diagram hdisc

end


end ArchonPhysics.EqualMassPeriodicFPUTLocalCollisionGridDiagonal
