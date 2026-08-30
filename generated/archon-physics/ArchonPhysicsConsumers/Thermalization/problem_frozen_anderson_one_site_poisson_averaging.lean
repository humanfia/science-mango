import ArchonPhysics.FrozenAndersonOneSitePoissonAveraging

/-!
# Consumer: eta-smoothed frozen Anderson one-site averaging

This consumer records the no-axiom endpoint currently available before a
Stone/projector limit: a sharp bounded-density Poisson estimate, its direct
`Uniform[4/5, 6/5]` frozen-mass Green expectation, and the corresponding
finite collection of conditional site estimates.
-/

namespace ArchonPhysicsConsumers.Thermalization.ProblemFrozenAndersonOneSitePoissonAveraging

open ArchonPhysics
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.FrozenAndersonOneSitePoissonAveraging
open MeasureTheory
open scoped BigOperators ENNReal Matrix

noncomputable section

/-- Sharp scalar Poisson/Herglotz averaging under a finite Lebesgue-density
ceiling. -/
theorem problem_frozenAnderson_poisson_boundedDensity
    {mu : Measure Real} {densityBound : ENNReal}
    (hdensityBound : densityBound ≠ ∞)
    (hmu : mu ≤ densityBound • (volume : Measure Real))
    (alpha : Complex) (halpha : 0 < alpha.im) :
    ∫ x : Real, -((alpha - (x : Complex))⁻¹).im ∂mu ≤
      densityBound.toReal * Real.pi :=
  integral_neg_im_inv_sub_real_le_of_measure_le
    hdensityBound hmu alpha halpha

/-- Direct frozen iid `Uniform[4/5, 6/5]` one-site smoothed spectral
averaging for every finite real Hermitian background. -/
theorem problem_frozenAnderson_uniform_oneSiteGreen_negIm
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : 0 < z.im)
    (reference lambda : Real) (hlambda : lambda ≠ 0) :
    ∫ mass : Real,
        -(finiteFrozenOneSiteGreen background i z lambda mass).im
          ∂massCoordinateLaw ≤
      (5 / 2 : Real) * |lambda|⁻¹ * Real.pi :=
  integral_finiteFrozenOneSiteGreen_neg_im_massCoordinateLaw_le
    background hbackground i z hz reference lambda hlambda

/-- Finite sum of the sharp conditional one-site estimates, one for each
site and its frozen Hermitian environment. -/
theorem problem_frozenAnderson_uniform_conditionalSiteSum
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : index → Matrix index index Real)
    (hbackground : ∀ i, (background i).IsHermitian)
    (z : Complex) (hz : 0 < z.im)
    (reference : index → Real) (lambda : Real) (hlambda : lambda ≠ 0) :
    ∑ i : index, ∫ mass : Real,
        -(finiteFrozenOneSiteGreen (background i) i z lambda mass).im
          ∂massCoordinateLaw ≤
      (Fintype.card index : Real) *
        ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi) :=
  sum_integral_finiteFrozenOneSiteGreen_neg_im_massCoordinateLaw_le
    background hbackground z hz reference lambda hlambda

#print axioms problem_frozenAnderson_poisson_boundedDensity
#print axioms problem_frozenAnderson_uniform_oneSiteGreen_negIm
#print axioms problem_frozenAnderson_uniform_conditionalSiteSum

end

end ArchonPhysicsConsumers.Thermalization.ProblemFrozenAndersonOneSitePoissonAveraging
