import ArchonPhysics.FiniteWindowIIDAllVolumeStrongLaw

/-!
# Complex fixed-window iid strong law at every volume

Applying the all-volume real strong law to real and imaginary parts gives a
complex-valued spatial strong law.  This is the probability interface needed
to recombine polynomial cosine and sine marked legs into a Fourier kernel.
-/

open scoped ComplexConjugate

namespace ArchonPhysics.ComplexFiniteWindowIIDAllVolumeStrongLaw

open ArchonPhysics
open ArchonPhysics.FiniteWindowIIDAllVolumeStrongLaw
open ArchonPhysics.FiniteWindowIIDStrongLaw
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A complex observable evaluated on one iid mass window. -/
def complexWindowObservable (ensemble : IIDMassPhaseEnsemble Omega)
    (W offset : Nat) (f : (Fin W → Real) → Complex)
    (k : Nat) (omega : Omega) : Complex :=
  f (massWindow ensemble W offset k omega)

/-- Ordinary all-volume complex spatial prefix average. -/
def complexSpatialAverage (ensemble : IIDMassPhaseEnsemble Omega)
    (W : Nat) (f : (Fin W → Real) → Complex)
    (n : Nat) (omega : Omega) : Complex :=
  (∑ i ∈ Finset.range n,
    complexWindowObservable ensemble W i f 0 omega) / (n : Real)

/-- The deterministic complex mean, assembled from Bochner integrals of the
real and imaginary parts. -/
def complexWindowMean (ensemble : IIDMassPhaseEnsemble Omega)
    (W : Nat) (f : (Fin W → Real) → Complex) : Complex :=
  (∫ omega, (complexWindowObservable ensemble W 0 f 0 omega).re
      ∂ensemble.probability) +
    (∫ omega, (complexWindowObservable ensemble W 0 f 0 omega).im
      ∂ensemble.probability) * Complex.I

theorem complexSpatialAverage_re
    (ensemble : IIDMassPhaseEnsemble Omega)
    (W : Nat) (f : (Fin W → Real) → Complex)
    (n : Nat) (omega : Omega) :
    (complexSpatialAverage ensemble W f n omega).re =
      (∑ i ∈ Finset.range n,
        windowObservable ensemble W i (fun x ↦ (f x).re) 0 omega) /
          (n : Real) := by
  simp [complexSpatialAverage, complexWindowObservable, windowObservable]

theorem complexSpatialAverage_im
    (ensemble : IIDMassPhaseEnsemble Omega)
    (W : Nat) (f : (Fin W → Real) → Complex)
    (n : Nat) (omega : Omega) :
    (complexSpatialAverage ensemble W f n omega).im =
      (∑ i ∈ Finset.range n,
        windowObservable ensemble W i (fun x ↦ (f x).im) 0 omega) /
          (n : Real) := by
  simp [complexSpatialAverage, complexWindowObservable, windowObservable]

/-- Every bounded measurable complex observable of a fixed iid mass window
obeys the ordinary all-volume sliding-window spatial strong law. -/
theorem complexSpatialAverage_allVolume_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (W : Nat) (hW : 0 < W)
    (f : (Fin W → Real) → Complex) (hf : Measurable f)
    (C : Real)
    (hbound : ∀ x : Fin W → Real,
      (∀ j, x j ∈ massSupport) → ‖f x‖ ≤ C) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto (fun n : Nat ↦ complexSpatialAverage ensemble W f n omega)
        atTop (𝓝 (complexWindowMean ensemble W f)) := by
  have hfre : Measurable (fun x ↦ (f x).re) :=
    Complex.reCLM.continuous.measurable.comp hf
  have hfim : Measurable (fun x ↦ (f x).im) :=
    Complex.imCLM.continuous.measurable.comp hf
  have hboundRe : ∀ x : Fin W → Real,
      (∀ j, x j ∈ massSupport) → ‖(f x).re‖ ≤ C := by
    intro x hx
    simpa [Real.norm_eq_abs] using
      (Complex.abs_re_le_norm (f x)).trans (hbound x hx)
  have hboundIm : ∀ x : Fin W → Real,
      (∀ j, x j ∈ massSupport) → ‖(f x).im‖ ≤ C := by
    intro x hx
    simpa [Real.norm_eq_abs] using
      (Complex.abs_im_le_norm (f x)).trans (hbound x hx)
  filter_upwards
    [spatialRangeWindowAverage_allVolume_strongLaw_ae
      ensemble W hW (fun x ↦ (f x).re) hfre C hboundRe,
    spatialRangeWindowAverage_allVolume_strongLaw_ae
      ensemble W hW (fun x ↦ (f x).im) hfim C hboundIm]
      with omega hre him
  let r : Nat → Real := fun n ↦
    (∑ i ∈ Finset.range n,
      windowObservable ensemble W i (fun x ↦ (f x).re) 0 omega) /
        (n : Real)
  let s : Nat → Real := fun n ↦
    (∑ i ∈ Finset.range n,
      windowObservable ensemble W i (fun x ↦ (f x).im) 0 omega) /
        (n : Real)
  have hre' : Tendsto r atTop
      (𝓝 (∫ omega,
        (complexWindowObservable ensemble W 0 f 0 omega).re
          ∂ensemble.probability)) := by
    simpa [r, complexWindowObservable, windowObservable] using hre
  have him' : Tendsto s atTop
      (𝓝 (∫ omega,
        (complexWindowObservable ensemble W 0 f 0 omega).im
          ∂ensemble.probability)) := by
    simpa [s, complexWindowObservable, windowObservable] using him
  have hcomplex :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hre').add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp him').mul_const
        Complex.I)
  apply hcomplex.congr'
  filter_upwards with n
  rw [← Complex.re_add_im (complexSpatialAverage ensemble W f n omega)]
  rw [complexSpatialAverage_re, complexSpatialAverage_im]
  rfl

end


end ArchonPhysics.ComplexFiniteWindowIIDAllVolumeStrongLaw
