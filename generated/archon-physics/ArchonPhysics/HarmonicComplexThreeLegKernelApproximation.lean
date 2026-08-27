import ArchonPhysics.HarmonicNormalizedEdgeFrame
import ArchonPhysics.ComplexThreeLegKernelApproximation

/-!
# Harmonic complex three-leg approximation

This module specializes the complex spectral-frame bounds to the explicit
normalized edge frame of a simple positive-mass harmonic cycle.  Effective
one-leg approximation bounds therefore give volume-uniform three-leg
replacement estimates without consumer-side factorization assumptions.
-/

open scoped BigOperators

namespace ArchonPhysics.HarmonicComplexThreeLegKernelApproximation

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.ComplexThreeLegKernelApproximation
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedInteractionSpectralFactorization
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeLegKernelApproximationAlgebra
open ArchonPhysics.ThreeWaveCollisionFourierFactorization

noncomputable section


/-- Direct complex effective-weight replacement bound for three harmonic
projected kernels.  The explicit harmonic edge frame discharges every
factorization, orthogonality, and row-energy hypothesis. -/
theorem harmonic_threeLeg_complexProjectedKernel_replacementPerSite_norm_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (weight polynomialWeight : Fin 3 → OrderedModeIndex N → Complex)
    (epsilon bound polynomialBound : Fin 3 → Real)
    (hepsilon : ∀ r, 0 ≤ epsilon r)
    (hbound : ∀ r, 0 ≤ bound r)
    (hpolynomialBound : ∀ r, 0 ≤ polynomialBound r)
    (hdifference : ∀ r k,
      ‖(orderedEigenvalue (harmonicHermitian m) k : Complex) * weight r k -
        (orderedEigenvalue (harmonicHermitian m) k : Complex) *
          polynomialWeight r k‖ ≤ epsilon r)
    (heffective : ∀ r k,
      ‖(orderedEigenvalue (harmonicHermitian m) k : Complex) * weight r k‖ ≤
        bound r)
    (hpolynomialEffective : ∀ r k,
      ‖(orderedEigenvalue (harmonicHermitian m) k : Complex) *
        polynomialWeight r k‖ ≤ polynomialBound r) :
    ‖((∑ j, ∑ l, ∏ r : Fin 3,
          complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
            (harmonicHermitian m) (weight r) j l) -
        (∑ j, ∑ l, ∏ r : Fin 3,
          complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
            (harmonicHermitian m) (polynomialWeight r) j l)) /
        ((N : Real) : Complex)‖ ≤
      epsilon 0 * bound 1 * bound 2 +
        epsilon 1 * polynomialBound 0 * bound 2 +
          epsilon 2 * polynomialBound 0 * polynomialBound 1 := by
  let u := harmonicNormalizedEdgeFrame m
  have hfactor := projectedBondKernel_eq_harmonicNormalizedEdgeFrame m hsimple
  have horth := harmonicNormalizedEdgeFrame_orthonormal m hsimple
  have hrow : ∀ j, rowEnergy u j ≤ 1 :=
    rowEnergy_le_one_of_orthonormal_of_card_eq u
      (by simp [Lattice.Site]) horth
  let K : (Fin 3 → OrderedModeIndex N → Complex) →
      Fin 3 → Lattice.Site N → Lattice.Site N → Complex :=
    fun w r ↦ complexWeightedProjectedBondKernel
      (massWeightedDifferenceMatrix m) (harmonicHermitian m) (w r)
  have hentry (r : Fin 3) : ∀ j l,
      ‖K weight r j l - K polynomialWeight r j l‖ ≤ epsilon r := by
    intro j l
    exact
      complexWeightedProjectedBondKernel_sub_entry_norm_le_of_effectiveWeight
        (massWeightedDifferenceMatrix m) (harmonicHermitian m)
        u hfactor hrow (weight r) (polynomialWeight r)
        (epsilon r) (hepsilon r) (hdifference r) j l
  have hfrob (w : Fin 3 → OrderedModeIndex N → Complex)
      (M : Fin 3 → Real) (hM : ∀ r, 0 ≤ M r)
      (hw : ∀ r k,
        ‖(orderedEigenvalue (harmonicHermitian m) k : Complex) * w r k‖ ≤
          M r)
      (r : Fin 3) :
      Real.sqrt (frobeniusSq (K w r)) ≤ Real.sqrt (N : Real) * M r := by
    simpa [K, Lattice.Site] using
      complexWeightedProjectedBondKernel_sqrt_frobeniusSq_le_of_effectiveWeight
        (massWeightedDifferenceMatrix m) (harmonicHermitian m)
        u hfactor horth (w r) (M r) (hM r) (hw r)
  have hmain := norm_tripleSum_sub_div_volume_le
    (K weight 0) (K weight 1) (K weight 2)
    (K polynomialWeight 0) (K polynomialWeight 1) (K polynomialWeight 2)
    (N : Real) (epsilon 0) (epsilon 1) (epsilon 2)
    (polynomialBound 0) (bound 1) (polynomialBound 1) (bound 2)
    (by exact_mod_cast NeZero.pos N)
    (hepsilon 0) (hepsilon 1) (hepsilon 2)
    (hpolynomialBound 0) (hbound 1)
    (hentry 0) (hentry 1) (hentry 2)
    (hfrob weight bound hbound heffective 1)
    (hfrob weight bound hbound heffective 2)
    (hfrob polynomialWeight polynomialBound hpolynomialBound
      hpolynomialEffective 0)
    (hfrob polynomialWeight polynomialBound hpolynomialBound
      hpolynomialEffective 1)
  simpa only [tripleSum, K, Fin.prod_univ_three] using hmain

/-- If the real and imaginary parts of every effective one-leg weight are
each approximated within `epsilon`, the complex three-leg per-site error is
controlled with the explicit componentwise constant `2 * epsilon`. -/
theorem
    harmonic_threeLeg_complexProjectedKernel_componentwiseReplacementPerSite_norm_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (weight polynomialWeight : Fin 3 → OrderedModeIndex N → Complex)
    (epsilon bound polynomialBound : Fin 3 → Real)
    (hepsilon : ∀ r, 0 ≤ epsilon r)
    (hbound : ∀ r, 0 ≤ bound r)
    (hpolynomialBound : ∀ r, 0 ≤ polynomialBound r)
    (hre : ∀ r k,
      |(((orderedEigenvalue (harmonicHermitian m) k : Complex) * weight r k -
        (orderedEigenvalue (harmonicHermitian m) k : Complex) *
          polynomialWeight r k).re)| ≤ epsilon r)
    (him : ∀ r k,
      |(((orderedEigenvalue (harmonicHermitian m) k : Complex) * weight r k -
        (orderedEigenvalue (harmonicHermitian m) k : Complex) *
          polynomialWeight r k).im)| ≤ epsilon r)
    (heffective : ∀ r k,
      ‖(orderedEigenvalue (harmonicHermitian m) k : Complex) * weight r k‖ ≤
        bound r)
    (hpolynomialEffective : ∀ r k,
      ‖(orderedEigenvalue (harmonicHermitian m) k : Complex) *
        polynomialWeight r k‖ ≤ polynomialBound r) :
    ‖((∑ j, ∑ l, ∏ r : Fin 3,
          complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
            (harmonicHermitian m) (weight r) j l) -
        (∑ j, ∑ l, ∏ r : Fin 3,
          complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
            (harmonicHermitian m) (polynomialWeight r) j l)) /
        ((N : Real) : Complex)‖ ≤
      (2 * epsilon 0) * bound 1 * bound 2 +
        (2 * epsilon 1) * polynomialBound 0 * bound 2 +
          (2 * epsilon 2) * polynomialBound 0 * polynomialBound 1 := by
  have hdifference (r : Fin 3) (k : OrderedModeIndex N) :
      ‖(orderedEigenvalue (harmonicHermitian m) k : Complex) * weight r k -
        (orderedEigenvalue (harmonicHermitian m) k : Complex) *
          polynomialWeight r k‖ ≤ 2 * epsilon r := by
    let z : Complex :=
      (orderedEigenvalue (harmonicHermitian m) k : Complex) * weight r k -
        (orderedEigenvalue (harmonicHermitian m) k : Complex) *
          polynomialWeight r k
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ epsilon r + epsilon r := add_le_add (hre r k) (him r k)
      _ = 2 * epsilon r := by ring
  exact harmonic_threeLeg_complexProjectedKernel_replacementPerSite_norm_le
    m hsimple weight polynomialWeight (fun r ↦ 2 * epsilon r)
    bound polynomialBound (fun r ↦ mul_nonneg (by norm_num) (hepsilon r))
    hbound hpolynomialBound hdifference heffective hpolynomialEffective

end
end ArchonPhysics.HarmonicComplexThreeLegKernelApproximation
