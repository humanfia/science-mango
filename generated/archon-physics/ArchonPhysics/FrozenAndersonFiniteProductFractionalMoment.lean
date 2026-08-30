import ArchonPhysics.FrozenAndersonFiniteProductSmoothedTraceWegner
import ArchonPhysics.FrozenMassOneSiteFractionalMoment

/-!
# Finite-product fractional moments for frozen iid Anderson masses

The one-site fractional Green estimate in
`FrozenMassOneSiteFractionalMoment` is quenched in every other matrix entry.
The coordinate-splitting/Fubini theorem in
`FrozenAndersonFiniteProductSmoothedTraceWegner` therefore lifts it to the
complete canonical finite iid mass law without a conditional-expectation
assumption.

For every finite real Hermitian background, every selected site, every
upper-half-plane spectral parameter, `0 < s < 1`, and `lambda != 0`, this
module proves

`E[|G_ii(z)|^s] <= (1 + 5 / (1-s)) |lambda|^(-s)`.

The constant is independent of the volume and of the frozen environment.
This is a genuine full-product diagonal fractional-moment estimate.  It does
not prove off-diagonal decay, spatial iteration, a Lyapunov exponent, or an
eigenfunction-correlator bound.
-/

namespace ArchonPhysics.FrozenAndersonFiniteProductFractionalMoment

open ArchonPhysics
open ArchonPhysics.FrozenAndersonFiniteProductSmoothedTraceWegner
open ArchonPhysics.FrozenAndersonOneSitePoissonAveraging
open ArchonPhysics.FrozenMassOneSiteFractionalMoment
open ArchonPhysics.RandomEnsemble
open MeasureTheory
open scoped BigOperators Matrix

noncomputable section

/-! ## Explicit section integrability -/

/-- The one-site fractional Green section is integrable under the actual
frozen mass law.  The published one-site bound already proves this fact
internally; it is exposed here because finite-product Fubini needs it as a
separate premise. -/
theorem integrable_norm_finiteFrozenOneSiteGreen_rpow_massCoordinateLaw
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real)
    (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : 0 < z.im)
    (reference : Real)
    {s lambda : Real} (hs0 : 0 < s) (hs1 : s < 1)
    (hlambda : lambda ≠ 0) :
    Integrable
      (fun mass : Real =>
        ‖finiteFrozenOneSiteGreen background i z lambda mass‖ ^ s)
      massCoordinateLaw := by
  let alpha :=
    oneSiteEffectiveHerglotzParameter background i z reference
  have hright :
      Integrable (fun mass : Real =>
        |alpha.re - lambda * mass| ^ (-s)) massCoordinateLaw := by
    simpa only [sub_eq_add_neg, neg_mul] using
      (integrable_affine_fractionalSingularPower_massCoordinateLaw
        hs0.le hs1 (neg_ne_zero.mpr hlambda)
        (a := alpha.re) (lambda := -lambda))
  have hgreen (mass : Real) :
      finiteFrozenOneSiteGreen background i z lambda mass =
        (alpha - ((lambda * mass : Real) : Complex))⁻¹ := by
    unfold finiteFrozenOneSiteGreen
    rw [finiteHermitianOneSiteGreen_eq_inv_sub
      background hbackground i z hz reference]
    rfl
  have hgreenMeas :
      AEStronglyMeasurable
        (fun mass : Real =>
          ‖finiteFrozenOneSiteGreen background i z lambda mass‖ ^ s)
        massCoordinateLaw := by
    have hdenom : Measurable
        (fun mass : Real =>
          alpha - ((lambda * mass : Real) : Complex)) := by
      fun_prop
    have hexplicit : Measurable
        (fun mass : Real =>
          ‖(alpha - ((lambda * mass : Real) : Complex))⁻¹‖ ^ s) :=
      hdenom.inv.norm.pow_const s
    exact hexplicit.aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun mass =>
        (congrArg (fun q : Complex => ‖q‖ ^ s) (hgreen mass)).symm)
  have hpointwise :
      ∀ᵐ mass ∂massCoordinateLaw,
        ‖finiteFrozenOneSiteGreen background i z lambda mass‖ ^ s ≤
          |alpha.re - lambda * mass| ^ (-s) := by
    filter_upwards [massCoordinateLaw.ae_ne (alpha.re / lambda)]
      with mass hmass
    have hrealne : alpha.re - lambda * mass ≠ 0 := by
      intro hzero
      apply hmass
      apply (eq_div_iff hlambda).2
      calc
        mass * lambda = lambda * mass := mul_comm _ _
        _ = alpha.re := by linarith
    have hrealpos : 0 < |alpha.re - lambda * mass| :=
      abs_pos.mpr hrealne
    have hnorm :
        |alpha.re - lambda * mass| ≤
          ‖alpha - ((lambda * mass : Real) : Complex)‖ := by
      simpa using
        (Complex.abs_re_le_norm
          (alpha - ((lambda * mass : Real) : Complex)))
    rw [hgreen mass, norm_inv,
      Real.inv_rpow
        (norm_nonneg (alpha - ((lambda * mass : Real) : Complex))),
      ← Real.rpow_neg
        (norm_nonneg (alpha - ((lambda * mass : Real) : Complex)))]
    exact Real.rpow_le_rpow_of_nonpos
      hrealpos hnorm (neg_nonpos.mpr hs0.le)
  exact hright.mono_nonneg hgreenMeas
    (Filter.Eventually.of_forall fun mass =>
      Real.rpow_nonneg
        (norm_nonneg
          (finiteFrozenOneSiteGreen background i z lambda mass)) _)
    hpointwise

/-! ## Full canonical iid finite-product estimate -/

/-- A full finite iid product estimate at one selected diagonal Green entry.
No abstract conditional probability object is used: `piFinSuccAbove` freezes
the complement and the same sharp one-site estimate is integrated by Fubini. -/
theorem integrable_and_integral_norm_finiteAndersonLocalGreen_rpow_canonicalFiniteIIDMassLaw
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (i : Fin (n + 1)) (z : Complex) (hz : 0 < z.im)
    {s : Real} (hs0 : 0 < s) (hs1 : s < 1) :
    Integrable
        (fun mass =>
          ‖finiteAndersonLocalGreen background lambda mass i z‖ ^ s)
        (canonicalFiniteIIDMassLaw (n + 1)) ∧
      integral (canonicalFiniteIIDMassLaw (n + 1))
          (fun mass =>
            ‖finiteAndersonLocalGreen background lambda mass i z‖ ^ s) ≤
        (1 + 5 / (1 - s)) * |lambda| ^ (-s) := by
  unfold canonicalFiniteIIDMassLaw
  apply finitePi_coordinate_integrable_and_integral_le
    massCoordinateLaw i
  · exact ((continuous_finiteAndersonLocalGreen
      background hbackground lambda i z hz.ne').measurable.norm.pow_const s)
  · positivity
  · intro mass
    exact Real.rpow_nonneg
      (norm_nonneg
        (finiteAndersonLocalGreen background lambda mass i z)) _
  · intro rest
    simpa only [finiteAndersonLocalGreen_eq_finiteFrozenOneSiteGreen] using
      integrable_norm_finiteFrozenOneSiteGreen_rpow_massCoordinateLaw
        (finiteAndersonFrozenBackground background lambda i rest)
        (finiteAndersonFrozenBackground_isHermitian
          background hbackground lambda i rest)
        i z hz 0 hs0 hs1 hlambda
  · intro rest
    simpa only [finiteAndersonLocalGreen_eq_finiteFrozenOneSiteGreen] using
      integral_norm_finiteFrozenOneSiteGreen_rpow_le
        (finiteAndersonFrozenBackground background lambda i rest)
        (finiteAndersonFrozenBackground_isHermitian
          background hbackground lambda i rest)
        i z hz 0 hs0 hs1 hlambda

/-- The sum of all diagonal fractional Green moments costs exactly the volume
times the same dimension-free one-site constant. -/
theorem integral_sum_norm_finiteAndersonLocalGreen_rpow_canonicalFiniteIIDMassLaw_le
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (z : Complex) (hz : 0 < z.im)
    {s : Real} (hs0 : 0 < s) (hs1 : s < 1) :
    integral (canonicalFiniteIIDMassLaw (n + 1))
        (fun mass => ∑ i : Fin (n + 1),
          ‖finiteAndersonLocalGreen background lambda mass i z‖ ^ s) ≤
      (n + 1 : Real) * ((1 + 5 / (1 - s)) * |lambda| ^ (-s)) := by
  rw [integral_finsetSum Finset.univ]
  · calc
      (∑ i : Fin (n + 1),
          integral (canonicalFiniteIIDMassLaw (n + 1))
            (fun mass =>
              ‖finiteAndersonLocalGreen background lambda mass i z‖ ^ s)) ≤
          ∑ _i : Fin (n + 1),
            ((1 + 5 / (1 - s)) * |lambda| ^ (-s)) := by
            apply Finset.sum_le_sum
            intro i _
            exact
              (integrable_and_integral_norm_finiteAndersonLocalGreen_rpow_canonicalFiniteIIDMassLaw
                background hbackground lambda hlambda i z hz hs0 hs1).2
      _ = (n + 1 : Real) *
          ((1 + 5 / (1 - s)) * |lambda| ^ (-s)) := by simp
  · intro i _
    exact
      (integrable_and_integral_norm_finiteAndersonLocalGreen_rpow_canonicalFiniteIIDMassLaw
        background hbackground lambda hlambda i z hz hs0 hs1).1

end

end ArchonPhysics.FrozenAndersonFiniteProductFractionalMoment
