import ArchonPhysics.ActualThreeSiteIteratedA2OuterConcreteGoodBad

/-!
# Final all-width quantitative small ball for the three-site outer channel

For arbitrary positive inverse-strip width `delta`, the support cutoff is
chosen explicitly as `min delta (1 / 10)`.  This keeps the inner cube inside
the physical support and makes its boundary loss no larger than `15 delta`.
The resulting atlas coefficient is finite for each `delta`; no uniform or
optimized dependence on `delta` is asserted.
-/

namespace ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBallFinal

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterConcreteGoodBad
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBall
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory
open scoped ENNReal

noncomputable section

/-- For every positive inverse-strip width there is a finite, possibly
`delta`-dependent coefficient giving the quantitative scalar small-ball
bound.  No estimate on that dependence is part of the statement. -/
theorem exists_finiteCoefficient_threeSiteOuter_quantitative_smallBall
    {delta : Real} (hdelta : 0 < delta) :
    ∃ coefficient : ENNReal, coefficient ≠ ∞ ∧
      ∀ epsilon : Real, 0 ≤ epsilon →
        iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
          25 * ENNReal.ofReal delta +
            coefficient * ENNReal.ofReal epsilon := by
  let eta : Real := min delta (1 / 10)
  have heta : 0 < eta := by
    simpa [eta] using lt_min hdelta (by norm_num : (0 : Real) < 1 / 10)
  have hetaLeDelta : eta ≤ delta := by
    exact min_le_left _ _
  have hetaLeTenth : eta ≤ (1 / 10 : Real) := by
    exact min_le_right _ _
  have hetaWidth : 2 * eta < massUpper - massLower := by
    norm_num [massUpper, massLower]
    linarith
  obtain ⟨coefficient, hcoefficientFinite, hsmallBall⟩ :=
    exists_finiteCoefficient_threeSiteOuter_twoParameter_smallBall
      hdelta heta hetaWidth
  refine ⟨coefficient, hcoefficientFinite, ?_⟩
  intro epsilon hepsilon
  have hetaENN : ENNReal.ofReal eta ≤ ENNReal.ofReal delta :=
    ENNReal.ofReal_le_ofReal hetaLeDelta
  calc
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
        10 * ENNReal.ofReal delta + 15 * ENNReal.ofReal eta +
          coefficient * ENNReal.ofReal epsilon :=
      hsmallBall epsilon hepsilon
    _ ≤ 10 * ENNReal.ofReal delta + 15 * ENNReal.ofReal delta +
        coefficient * ENNReal.ofReal epsilon := by
      exact add_le_add
        (add_le_add le_rfl (mul_le_mul le_rfl hetaENN bot_le bot_le)) le_rfl
    _ = 25 * ENNReal.ofReal delta +
        coefficient * ENNReal.ofReal epsilon := by ring

end

end ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBallFinal
