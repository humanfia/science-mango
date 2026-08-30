import ArchonPhysics.FrozenMassOneSiteFractionalMoment

/-!
# Consumer: frozen-mass one-site fractional moments

This consumer replays the explicit `0 < s < 1` affine singular average, its
single scalar Schur step, and the actual finite-volume local Green bound.  The
finite background is quenched and only one fresh `Uniform[4/5,6/5]` mass is
averaged.  No iid conditional reconstruction, spatial contraction, EFC decay,
thermodynamic limit, or Markov closure is asserted.
-/

namespace ArchonPhysicsConsumers.Thermalization.ProblemFrozenMassOneSiteFractionalMoment

open ArchonPhysics
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.FrozenAndersonOneSitePoissonAveraging
open ArchonPhysics.FrozenMassOneSiteFractionalMoment
open MeasureTheory
open scoped ENNReal Matrix

noncomputable section

/-- Exact analytic normalization of the truncated singular kernel. -/
example {s : Real} (hs : s < 1) :
    ∫ x : Real, unitFractionalSingularKernel s x =
      2 / (1 - s) :=
  integral_unitFractionalSingularKernel hs

/-- Actual frozen-law affine fractional moment, uniform in the center. -/
example {s a lambda : Real} (hs0 : 0 < s) (hs1 : s < 1)
    (hlambda : lambda ≠ 0) :
    (∫ mass : Real, |a + lambda * mass| ^ (-s)
        ∂massCoordinateLaw) ≤
      (1 + 5 / (1 - s)) * |lambda| ^ (-s) :=
  integral_affine_fractionalSingularPower_massCoordinateLaw_le
    hs0.le hs1 hlambda

/-- Exact scalar Schur step with a fixed environment tail. -/
example {s a lambda hop tail : Real}
    (hs0 : 0 < s) (hs1 : s < 1) (hlambda : lambda ≠ 0) :
    (∫ mass : Real,
        |scalarOneSiteSchurTransfer a lambda hop tail mass| ^ s
          ∂massCoordinateLaw) ≤
      ((1 + 5 / (1 - s)) * |lambda| ^ (-s) * |hop| ^ s) *
        |tail| ^ s :=
  integral_scalarOneSiteSchurTransfer_rpow_le
    hs0.le hs1 hlambda

/-- The transparent `q < 1` large-disorder/weak-hop condition gives strict
one-step contraction for every nonzero fixed tail. -/
example {s a lambda hop tail : Real}
    (hs0 : 0 < s) (hs1 : s < 1) (hlambda : lambda ≠ 0)
    (htail : tail ≠ 0)
    (hq : scalarOneSiteFractionalMomentFactor s lambda hop < 1) :
    (∫ mass : Real,
        |scalarOneSiteSchurTransfer a lambda hop tail mass| ^ s
          ∂massCoordinateLaw) < |tail| ^ s :=
  integral_scalarOneSiteSchurTransfer_rpow_lt_tail
    hs0 hs1 hlambda htail hq

/-- Actual finite-volume Hermitian local Green function, with a dimension-free
one-site constant and an explicit upper-half-plane resolvent condition. -/
example {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real)
    (hbackground : background.IsHermitian)
    (i : index) (z : Complex) (hz : 0 < z.im)
    (reference : Real)
    {s lambda : Real} (hs0 : 0 < s) (hs1 : s < 1)
    (hlambda : lambda ≠ 0) :
    (∫ mass : Real,
        ‖finiteFrozenOneSiteGreen background i z lambda mass‖ ^ s
          ∂massCoordinateLaw) ≤
      (1 + 5 / (1 - s)) * |lambda| ^ (-s) :=
  integral_norm_finiteFrozenOneSiteGreen_rpow_le
    background hbackground i z hz reference hs0 hs1 hlambda

#print axioms integral_unitFractionalSingularKernel
#print axioms integral_translatedUnitFractionalSingularKernel_massCoordinateLaw_le
#print axioms measurable_fractionalSingularPower
#print axioms integral_fractionalSingularPower_massCoordinateLaw_le
#print axioms integral_affine_fractionalSingularPower_massCoordinateLaw_le
#print axioms abs_scalarOneSiteSchurGreen_rpow
#print axioms integral_scalarOneSiteSchurTransfer_rpow_le
#print axioms integral_scalarOneSiteSchurTransfer_rpow_lt_tail
#print axioms frozenMassCoordinateLawNullSingletonClass
#print axioms integral_norm_finiteFrozenOneSiteGreen_rpow_le

end

end ArchonPhysicsConsumers.Thermalization.ProblemFrozenMassOneSiteFractionalMoment
