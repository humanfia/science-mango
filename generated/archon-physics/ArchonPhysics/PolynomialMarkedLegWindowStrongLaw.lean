import ArchonPhysics.FiniteWindowIIDStrongLaw
import ArchonPhysics.PeriodicWeightedCycleBlockGluing
import ArchonPhysics.RegularizedMarkedLegPolynomialLocality

/-!
# Fixed-polynomial marked-leg window strong laws

This file connects the finite-propagation algebra for a fixed zero-constant
spectral polynomial with the strong law for finite iid mass windows.  The
local observable below is a fixed entry of the polynomial weighted-cycle
kernel on a finite window.  Clipping is built into the definition, so the
reciprocal mass is everywhere measurable and the observable is uniformly
bounded through its compact finite-product range.

The final probability theorem recombines every residue class of disjoint
windows.  It is a fixed-polynomial statement only: no passage to a continuous
spectral weight or to the unregularized collision measure is asserted.
-/

open scoped Matrix

namespace ArchonPhysics.PolynomialMarkedLegWindowStrongLaw

open ArchonPhysics
open ArchonPhysics.FiniteWindowIIDStrongLaw
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.OrderedInteractionSpectralFactorization
open ArchonPhysics.OrderedInteractionSpectralFactorization.Harmonic
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RegularizedMarkedLegPolynomialLocality
open Filter MeasureTheory ProbabilityTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Coordinatewise clipping of a finite mass window. -/
def clipWindow {W : Nat} (x : Fin W → Real) : Fin W → Real :=
  fun i ↦ clippedMass (x i)

/-- Inverse clipped masses, used as the weighted-cycle edge field. -/
def inverseClippedWindow {W : Nat} (x : Fin W → Real) : Fin W → Real :=
  fun i ↦ (clippedMass (x i))⁻¹

/-- A fixed entry of the zero-constant polynomial weighted-cycle kernel on a
finite mass window. -/
def polynomialWindowKernelEntry {W : Nat} [NeZero W]
    (degree : Nat) (coefficient : Nat → Real) (a b : Fin W)
    (x : Fin W → Real) : Real :=
  zeroConstantMatrixPolynomialUpTo degree coefficient
    (finWeightedCycleLaplacian (inverseClippedWindow x)) a b

theorem continuous_clippedMass : Continuous clippedMass := by
  unfold clippedMass
  fun_prop

theorem clippedMass_ne_zero (x : Real) : clippedMass x ≠ 0 :=
  ne_of_gt (clippedMass_pos x)

theorem continuous_inverseClippedWindow_coordinate {W : Nat} (i : Fin W) :
    Continuous (fun x : Fin W → Real ↦ inverseClippedWindow x i) := by
  exact (continuous_clippedMass.comp (continuous_apply i)).inv₀
    (fun x ↦ clippedMass_ne_zero (x i))

theorem continuous_finWeightedCycleLaplacian_inverseClipped_apply
    {W : Nat} [NeZero W] (a b : Fin W) :
    Continuous (fun x : Fin W → Real ↦
      finWeightedCycleLaplacian (inverseClippedWindow x) a b) := by
  simp_rw [finWeightedCycleLaplacian_eq_sum_rankOne, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  exact continuous_finsetSum Finset.univ (fun i _hi ↦
    (continuous_inverseClippedWindow_coordinate i).mul continuous_const)

theorem continuous_matrixPow_apply
    {X iota : Type*} [TopologicalSpace X]
    [Fintype iota] [DecidableEq iota]
    (M : X → Matrix iota iota Real)
    (hM : ∀ i j, Continuous (fun x ↦ M x i j))
    (n : Nat) (i j : iota) :
    Continuous (fun x ↦ (M x ^ n) i j) := by
  induction n generalizing i j with
  | zero =>
      change Continuous (fun _ : X ↦ (1 : Matrix iota iota Real) i j)
      exact continuous_const
  | succ n ih =>
      simp_rw [pow_succ, Matrix.mul_apply]
      exact continuous_finsetSum Finset.univ (fun k _hk ↦
        (ih i k).mul (hM k j))

theorem continuous_polynomialWindowKernelEntry {W : Nat} [NeZero W]
    (degree : Nat) (coefficient : Nat → Real) (a b : Fin W) :
    Continuous (polynomialWindowKernelEntry degree coefficient a b) := by
  unfold polynomialWindowKernelEntry zeroConstantMatrixPolynomialUpTo
  simp_rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact continuous_finsetSum (Finset.range (degree + 1)) (fun n _hn ↦
    continuous_const.mul
      (continuous_matrixPow_apply
        (fun x ↦ finWeightedCycleLaplacian (inverseClippedWindow x))
        continuous_finWeightedCycleLaplacian_inverseClipped_apply
        (n + 1) a b))

theorem measurable_polynomialWindowKernelEntry {W : Nat} [NeZero W]
    (degree : Nat) (coefficient : Nat → Real) (a b : Fin W) :
    Measurable (polynomialWindowKernelEntry degree coefficient a b) :=
  (continuous_polynomialWindowKernelEntry degree coefficient a b).measurable

/-- The polynomial window observable is unchanged by clipping its whole
input.  This is the factorization through the compact product support. -/
theorem polynomialWindowKernelEntry_clipWindow {W : Nat} [NeZero W]
    (degree : Nat) (coefficient : Nat → Real) (a b : Fin W)
    (x : Fin W → Real) :
    polynomialWindowKernelEntry degree coefficient a b (clipWindow x) =
      polynomialWindowKernelEntry degree coefficient a b x := by
  unfold polynomialWindowKernelEntry inverseClippedWindow clipWindow
  congr 3
  funext i
  rw [clippedMass_eq_self (clippedMass_mem_support (x i))]

/-- Every fixed polynomial window entry admits a deterministic uniform bound
on all inputs.  The proof uses the compact frozen mass cube after clipping. -/
theorem exists_uniformBound_polynomialWindowKernelEntry
    {W : Nat} [NeZero W]
    (degree : Nat) (coefficient : Nat → Real) (a b : Fin W) :
    ∃ C : Real, ∀ x : Fin W → Real,
      ‖polynomialWindowKernelEntry degree coefficient a b x‖ ≤ C := by
  let K : Set (Fin W → Real) :=
    Set.pi Set.univ (fun _ ↦ massSupport)
  have hK : IsCompact K := by
    exact isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  let g : (Fin W → Real) → Real :=
    fun x ↦ ‖polynomialWindowKernelEntry degree coefficient a b x‖
  have hg : Continuous g :=
    (continuous_polynomialWindowKernelEntry degree coefficient a b).norm
  have hcompact : IsCompact (g '' K) := hK.image hg
  rcases hcompact.bddAbove with ⟨C, hC⟩
  refine ⟨C, fun x ↦ ?_⟩
  rw [← polynomialWindowKernelEntry_clipWindow degree coefficient a b x]
  apply hC
  refine ⟨clipWindow x, ?_, rfl⟩
  intro i _hi
  exact clippedMass_mem_support (x i)

/-- Average of the `W` disjoint residue-class averages.  For positive `W`
this is the spatial average over the first `W*n` window starting positions,
written in the form directly supplied by the block strong laws. -/
def recombinedWindowAverage
    (ensemble : IIDMassPhaseEnsemble Omega) (W : Nat)
    (f : (Fin W → Real) → Real) (n : Nat) (omega : Omega) : Real :=
  (1 / (W : Real)) *
    ∑ offset : Fin W,
      (∑ k ∈ Finset.range n,
        windowObservable ensemble W offset.val f k omega) / (n : Real)

/-- Exact reindexing of all residue classes into one initial interval. -/
theorem sum_residueClasses_eq_sum_range
    {M : Type*} [AddCommMonoid M]
    (W n : Nat) (F : Nat → M) :
    (∑ offset : Fin W, ∑ k ∈ Finset.range n,
      F (W * k + offset.val)) =
      ∑ i ∈ Finset.range (W * n), F i := by
  simp_rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_comm]
  rw [← Fintype.sum_prod_type
    (fun p : Fin n × Fin W ↦ F (W * p.1.val + p.2.val))]
  let e : Fin n × Fin W ≃ Fin (W * n) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm n W))
  exact Fintype.sum_equiv e _ _
    (fun p ↦ by simp [e, finProdFinEquiv, Nat.add_comm])

/-- The residue-class expression is exactly the ordinary sliding-window
spatial average over the first `W*n` starting sites. -/
theorem recombinedWindowAverage_eq_spatialRangeAverage
    (ensemble : IIDMassPhaseEnsemble Omega)
    (W : Nat) (hW : 0 < W)
    (f : (Fin W → Real) → Real) (n : Nat) (omega : Omega) :
    recombinedWindowAverage ensemble W f n omega =
      (∑ i ∈ Finset.range (W * n),
        windowObservable ensemble W i f 0 omega) / ((W * n : Nat) : Real) := by
  by_cases hn : n = 0
  · subst n
    simp [recombinedWindowAverage]
  · have hsum := sum_residueClasses_eq_sum_range W n
      (fun i ↦ windowObservable ensemble W i f 0 omega)
    have hwindow (offset : Fin W) (k : Nat) :
        windowObservable ensemble W offset.val f k omega =
          windowObservable ensemble W (W * k + offset.val) f 0 omega := by
      unfold windowObservable
      congr 1
      funext j
      simp [massWindow, Nat.add_assoc]
    have hsumEq :
        (∑ offset : Fin W, ∑ k ∈ Finset.range n,
          windowObservable ensemble W offset.val f k omega) =
        ∑ i ∈ Finset.range (W * n),
          windowObservable ensemble W i f 0 omega := by
      calc
        _ = ∑ offset : Fin W, ∑ k ∈ Finset.range n,
              windowObservable ensemble W (W * k + offset.val) f 0 omega := by
            apply Finset.sum_congr rfl
            intro offset _hoffset
            apply Finset.sum_congr rfl
            intro k _hk
            exact hwindow offset k
        _ = _ := hsum
    unfold recombinedWindowAverage
    rw [← Finset.sum_div, hsumEq]
    push_cast
    field_simp [ne_of_gt hW, hn]

/-- Fixed-window iid strong law after recombining all residue classes. -/
theorem recombinedWindowAverage_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (W : Nat) (hW : 0 < W)
    (f : (Fin W → Real) → Real) (hf : Measurable f)
    (C : Real)
    (hbound : ∀ x : Fin W → Real,
      (∀ j, x j ∈ massSupport) → ‖f x‖ ≤ C) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto (fun n : Nat ↦
        recombinedWindowAverage ensemble W f n omega) atTop
        (𝓝 (∫ omega,
          windowObservable ensemble W 0 f 0 omega
            ∂ensemble.probability)) := by
  filter_upwards
    [allOffsets_windowObservable_strongLaw_ae
      ensemble W f hf C hbound] with omega homega
  let mu : Real := ∫ omega,
    windowObservable ensemble W 0 f 0 omega ∂ensemble.probability
  have hoffset (offset : Fin W) :
      Tendsto
        (fun n : Nat ↦
          (∑ k ∈ Finset.range n,
            windowObservable ensemble W offset.val f k omega) / (n : Real))
        atTop (𝓝 mu) := by
    have h := homega offset
    have hwindow :=
      (massWindow_hasLaw ensemble W offset.val 0).identDistrib
        (massWindow_hasLaw ensemble W 0 0)
    have hident := hwindow.comp hf
    have hmean :
        (∫ omega,
          windowObservable ensemble W offset.val f 0 omega
            ∂ensemble.probability) = mu := by
      simpa [mu, windowObservable, Function.comp_def] using hident.integral_eq
    simpa [mu, hmean] using h
  have hsum :
      Tendsto
        (fun n : Nat ↦ ∑ offset : Fin W,
          (∑ k ∈ Finset.range n,
            windowObservable ensemble W offset.val f k omega) / (n : Real))
        atTop (𝓝 (∑ _offset : Fin W, mu)) := by
    exact tendsto_finsetSum Finset.univ (fun offset _hoffset ↦ hoffset offset)
  have hscaled :
      Tendsto
        (fun n : Nat ↦ (1 / (W : Real)) *
          ∑ offset : Fin W,
            (∑ k ∈ Finset.range n,
              windowObservable ensemble W offset.val f k omega) / (n : Real))
        atTop
        (𝓝 ((1 / (W : Real)) * ∑ _offset : Fin W, mu)) :=
    tendsto_const_nhds.mul hsum
  simpa [recombinedWindowAverage, mu, hW.ne'] using hscaled

/-- Ordinary sliding-window spatial average strong law along volumes `W*n`. -/
theorem spatialRangeWindowAverage_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (W : Nat) (hW : 0 < W)
    (f : (Fin W → Real) → Real) (hf : Measurable f)
    (C : Real)
    (hbound : ∀ x : Fin W → Real,
      (∀ j, x j ∈ massSupport) → ‖f x‖ ≤ C) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat ↦
          (∑ i ∈ Finset.range (W * n),
            windowObservable ensemble W i f 0 omega) /
              ((W * n : Nat) : Real))
        atTop
        (𝓝 (∫ omega,
          windowObservable ensemble W 0 f 0 omega
            ∂ensemble.probability)) := by
  filter_upwards
    [recombinedWindowAverage_strongLaw_ae
      ensemble W hW f hf C hbound] with omega homega
  refine homega.congr' (Eventually.of_forall fun n ↦ ?_)
  exact recombinedWindowAverage_eq_spatialRangeAverage
    ensemble W hW f n omega

/-- The fixed zero-constant polynomial marked-leg window entry has an almost
sure, deterministic block-recombined spatial mean. -/
theorem polynomialWindowKernelEntry_strongLaw_ae
    {W : Nat} [NeZero W]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (degree : Nat) (coefficient : Nat → Real) (a b : Fin W) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto (fun n : Nat ↦
        recombinedWindowAverage ensemble W
          (polynomialWindowKernelEntry degree coefficient a b) n omega)
        atTop
        (𝓝 (∫ omega,
          windowObservable ensemble W 0
            (polynomialWindowKernelEntry degree coefficient a b) 0 omega
              ∂ensemble.probability)) := by
  obtain ⟨C, hC⟩ :=
    exists_uniformBound_polynomialWindowKernelEntry
      degree coefficient a b
  exact recombinedWindowAverage_strongLaw_ae ensemble W (NeZero.pos W)
    (polynomialWindowKernelEntry degree coefficient a b)
    (measurable_polynomialWindowKernelEntry degree coefficient a b)
    C (fun x _hx ↦ hC x)

/-- Exact finite-volume three-leg factorization after replacing each marked
regularized leg by a fixed zero-constant spectral polynomial.  The right side
contains only local polynomial weighted-cycle kernels. -/
theorem harmonicThreeLegPolynomialMoment_factorization
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (degree : Fin 3 → Nat)
    (coefficient : Fin 3 → Nat → Real) :
    harmonicWeightedInteractionMoment m
        (fun r ↦ spectralPolynomialWeight (harmonicHermitian m)
          (degree r) (coefficient r)) =
      ∑ j, ∑ l, ∏ r : Fin 3,
        zeroConstantMatrixPolynomialUpTo (degree r) (coefficient r)
          (weightedCycleLaplacian (fun i ↦ (m.mass i)⁻¹)) j l := by
  rw [harmonicWeightedInteractionMoment_eq_projectedKernelProduct]
  simp_rw [harmonicWeightedProjectedBondKernel_spectralPolynomial_eq_weightedCycle
    m hsimple]

/-- Per-site form of the exact fixed-polynomial three-leg factorization. -/
theorem harmonicThreeLegPolynomialMoment_perSite_factorization
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (degree : Fin 3 → Nat)
    (coefficient : Fin 3 → Nat → Real) :
    harmonicWeightedInteractionMoment m
          (fun r ↦ spectralPolynomialWeight (harmonicHermitian m)
            (degree r) (coefficient r)) / (N : Real) =
      (∑ j, ∑ l, ∏ r : Fin 3,
        zeroConstantMatrixPolynomialUpTo (degree r) (coefficient r)
          (weightedCycleLaplacian (fun i ↦ (m.mass i)⁻¹)) j l) /
        (N : Real) := by
  rw [harmonicThreeLegPolynomialMoment_factorization
    m hsimple degree coefficient]

/-- Natural indices within `radius` of either side of the linear cut in a
length-`N` periodic chain.  Polynomial propagation of radius `radius` can
only notice the chosen cut at these indices. -/
def linearCutBoundaryIndices (N radius : Nat) : Finset Nat :=
  Finset.range (min radius N) ∪
    Finset.Ico (N - min radius N) N

theorem linearCutBoundaryIndices_subset_range (N radius : Nat) :
    linearCutBoundaryIndices N radius ⊆ Finset.range N := by
  intro i hi
  simp only [linearCutBoundaryIndices, Finset.mem_union, Finset.mem_range,
    Finset.mem_Ico] at hi ⊢
  omega

/-- At most twice the propagation radius is affected by opening the periodic
chain at one cut. -/
theorem card_linearCutBoundaryIndices_le (N radius : Nat) :
    (linearCutBoundaryIndices N radius).card ≤ 2 * radius := by
  calc
    (linearCutBoundaryIndices N radius).card ≤
        (Finset.range (min radius N)).card +
          (Finset.Ico (N - min radius N) N).card := by
      exact Finset.card_union_le _ _
    _ = 2 * min radius N := by
      simp
      omega
    _ ≤ 2 * radius := by omega

/-- For a fixed polynomial degree, the fraction of sites whose propagation
window meets the chosen periodic cut vanishes like `O((degree+1)/N)`. -/
theorem polynomialBoundaryFraction_tendsto_zero (degree : Nat) :
    Tendsto
      (fun N : Nat ↦
        ((linearCutBoundaryIndices N (degree + 1)).card : Real) / (N : Real))
      atTop (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero
    (b := 0) (B := ((2 * (degree + 1) : Nat) : Real))
  · exact Eventually.of_forall fun N ↦ by positivity
  · exact Eventually.of_forall fun N ↦ by
      exact_mod_cast card_linearCutBoundaryIndices_le N (degree + 1)
  · exact tendsto_natCast_atTop_atTop

/-- Product of three fixed polynomial marked-leg window entries.  This is the
local finite-window observable produced by the three-leg Fourier
factorization after each regularized scalar weight is replaced by a fixed
zero-constant polynomial. -/
def threeLegPolynomialWindowProduct {W : Nat} [NeZero W]
    (degree : Fin 3 → Nat)
    (coefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W)
    (x : Fin W → Real) : Real :=
  ∏ r : Fin 3, polynomialWindowKernelEntry
    (degree r) (coefficient r) (left r) (right r) x

theorem continuous_threeLegPolynomialWindowProduct
    {W : Nat} [NeZero W]
    (degree : Fin 3 → Nat)
    (coefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W) :
    Continuous (threeLegPolynomialWindowProduct
      degree coefficient left right) := by
  unfold threeLegPolynomialWindowProduct
  exact continuous_finsetProd Finset.univ (fun r _hr ↦
    continuous_polynomialWindowKernelEntry
      (degree r) (coefficient r) (left r) (right r))

theorem measurable_threeLegPolynomialWindowProduct
    {W : Nat} [NeZero W]
    (degree : Fin 3 → Nat)
    (coefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W) :
    Measurable (threeLegPolynomialWindowProduct
      degree coefficient left right) :=
  (continuous_threeLegPolynomialWindowProduct
    degree coefficient left right).measurable

theorem threeLegPolynomialWindowProduct_clipWindow
    {W : Nat} [NeZero W]
    (degree : Fin 3 → Nat)
    (coefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W)
    (x : Fin W → Real) :
    threeLegPolynomialWindowProduct degree coefficient left right
        (clipWindow x) =
      threeLegPolynomialWindowProduct degree coefficient left right x := by
  unfold threeLegPolynomialWindowProduct
  apply Finset.prod_congr rfl
  intro r _hr
  exact polynomialWindowKernelEntry_clipWindow
    (degree r) (coefficient r) (left r) (right r) x

theorem exists_uniformBound_threeLegPolynomialWindowProduct
    {W : Nat} [NeZero W]
    (degree : Fin 3 → Nat)
    (coefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W) :
    ∃ C : Real, ∀ x : Fin W → Real,
      ‖threeLegPolynomialWindowProduct degree coefficient left right x‖ ≤ C := by
  let K : Set (Fin W → Real) :=
    Set.pi Set.univ (fun _ ↦ massSupport)
  have hK : IsCompact K := by
    exact isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  let g : (Fin W → Real) → Real := fun x ↦
    ‖threeLegPolynomialWindowProduct degree coefficient left right x‖
  have hg : Continuous g :=
    (continuous_threeLegPolynomialWindowProduct
      degree coefficient left right).norm
  have hcompact : IsCompact (g '' K) := hK.image hg
  rcases hcompact.bddAbove with ⟨C, hC⟩
  refine ⟨C, fun x ↦ ?_⟩
  rw [← threeLegPolynomialWindowProduct_clipWindow
    degree coefficient left right x]
  apply hC
  refine ⟨clipWindow x, ?_, rfl⟩
  intro i _hi
  exact clippedMass_mem_support (x i)

/-- Almost-sure deterministic spatial mean for a product of three fixed
polynomial marked-leg window entries. -/
theorem threeLegPolynomialWindowProduct_strongLaw_ae
    {W : Nat} [NeZero W]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (degree : Fin 3 → Nat)
    (coefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto (fun n : Nat ↦
        recombinedWindowAverage ensemble W
          (threeLegPolynomialWindowProduct
            degree coefficient left right) n omega)
        atTop
        (𝓝 (∫ omega,
          windowObservable ensemble W 0
            (threeLegPolynomialWindowProduct
              degree coefficient left right) 0 omega
              ∂ensemble.probability)) := by
  obtain ⟨C, hC⟩ :=
    exists_uniformBound_threeLegPolynomialWindowProduct
      degree coefficient left right
  exact recombinedWindowAverage_strongLaw_ae ensemble W (NeZero.pos W)
    (threeLegPolynomialWindowProduct degree coefficient left right)
    (measurable_threeLegPolynomialWindowProduct
      degree coefficient left right)
    C (fun x _hx ↦ hC x)

/-- Ordinary first-`W*n` spatial average limit for the product of three fixed
polynomial marked-leg window entries. -/
theorem threeLegPolynomialWindowProduct_spatialRange_strongLaw_ae
    {W : Nat} [NeZero W]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (degree : Fin 3 → Nat)
    (coefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat ↦
          (∑ i ∈ Finset.range (W * n),
            windowObservable ensemble W i
              (threeLegPolynomialWindowProduct
                degree coefficient left right) 0 omega) /
                  ((W * n : Nat) : Real))
        atTop
        (𝓝 (∫ omega,
          windowObservable ensemble W 0
            (threeLegPolynomialWindowProduct
              degree coefficient left right) 0 omega
              ∂ensemble.probability)) := by
  obtain ⟨C, hC⟩ :=
    exists_uniformBound_threeLegPolynomialWindowProduct
      degree coefficient left right
  exact spatialRangeWindowAverage_strongLaw_ae
    ensemble W (NeZero.pos W)
    (threeLegPolynomialWindowProduct degree coefficient left right)
    (measurable_threeLegPolynomialWindowProduct
      degree coefficient left right)
    C (fun x _hx ↦ hC x)

end

end ArchonPhysics.PolynomialMarkedLegWindowStrongLaw
