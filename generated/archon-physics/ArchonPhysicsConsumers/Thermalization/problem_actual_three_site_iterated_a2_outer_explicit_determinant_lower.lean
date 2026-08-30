import ArchonPhysics.ActualThreeSiteIteratedA2OuterExplicitDeterminantLower
import ArchonPhysics.ActualThreeSiteIteratedA2OuterConcreteGoodBad

/-!
# Consumer: explicit determinant lower bound on the three-site good compact

The boundary cutoff `eta = min delta (1 / 10)` puts the concrete good set in
the interior iid support.  Its inverse-mass separation then feeds directly
into the pointwise core estimate, giving `|det| >= delta^2 / 4000`.

This does not turn the final compact-atlas small-ball coefficient into an
explicit function of `delta`: the cardinality of the inverse-function atlas
is still obtained from an existential finite subcover.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterCompactAtlas
open ArchonPhysics.ActualThreeSiteIteratedA2OuterConcreteGoodBad
open ArchonPhysics.ActualThreeSiteIteratedA2OuterExplicitDeterminantLower
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Set

noncomputable section

theorem threeSiteOuterGoodCompact_augmentedDet_ge_delta_sq_div_fourThousand
    {delta eta : Real} (hdelta : 0 < delta) (heta : 0 < eta)
    {triple : MassTriple}
    (htriple : triple ∈ threeSiteOuterGoodCompact delta eta) :
    delta ^ 2 / 4000 ≤
      |(threeSiteOuterAugmentedDerivative triple).det| := by
  exact
    abs_det_threeSiteOuterAugmentedDerivative_ge_delta_sq_div_fourThousand
      hdelta (threeSiteOuterGoodCompact_subset_interior heta htriple)
      (delta_le_abs_inverseSub_of_mem_threeSiteOuterGoodCompact heta htriple)

theorem threeSiteOuterMinCutoffGoodCompact_augmentedDet_ge_delta_sq_div_fourThousand
    {delta : Real} (hdelta : 0 < delta) {triple : MassTriple}
    (htriple : triple ∈
      threeSiteOuterGoodCompact delta (min delta (1 / 10))) :
    delta ^ 2 / 4000 ≤
      |(threeSiteOuterAugmentedDerivative triple).det| := by
  apply threeSiteOuterGoodCompact_augmentedDet_ge_delta_sq_div_fourThousand
    hdelta (lt_min hdelta (by norm_num : (0 : Real) < 1 / 10)) htriple

end

end ArchonPhysicsConsumers.Thermalization
