import ArchonPhysics.ActualTwoMassChildRepeatedMismatchLowerBound

/-!
# Consumer: actual two-mass ChildRepeated reverse-coarea lower bound

This consumer exposes the strongest presently unconditional analytic bridge.
The remaining model datum is a resonance-centred regular patch (and, for the
canonical endpoint, a cross-volume uniform family of such patches).
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedMismatchLowerBound
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Consumer-facing local linear-small-ball certificate. -/
theorem actualTwoMass_childRepeated_localLinearSmallBall
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N)
    (parent child : Fin (Fintype.card (Lattice.Site N)))
    {patch : Set (Real × Real)} (hpatch : MeasurableSet patch)
    (hpatchSupport : patch ⊆ iidMassPairSupport)
    (hderivative : ∀ point ∈ patch,
      HasFDerivWithinAt
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ parent child)
        (actualTwoMassChildFrequencyJacobian
          fixed site₁ site₂ parent child point) patch point)
    (hinjective : InjOn
      (actualTwoMassChildFrequencyChart
        fixed site₁ site₂ parent child) patch)
    {detUpper : Real} (hdetUpper : 0 < detUpper)
    (hdet : ∀ point ∈ patch,
      |(actualTwoMassChildFrequencyJacobian
        fixed site₁ site₂ parent child point).det| ≤ detUpper)
    {childSet : Set Real} (hchild : MeasurableSet childSet)
    (hchildPos : 0 < (volume : Measure Real) childSet)
    (hchildFinite : (volume : Measure Real) childSet ≠ ∞)
    {radius : Real} (hradius : 0 < radius)
    (hrectangle : childSet ×ˢ absoluteMismatchSublevel radius ⊆
      childFrequencyMismatchLinearEquiv ''
        (actualTwoMassChildFrequencyChart
          fixed site₁ site₂ parent child '' patch)) :
    ∃ constant : Real, 0 < constant ∧
      ∀ delta : Real, 0 < delta → delta ≤ radius →
        constant * delta ≤
          (Measure.map childRepeatedDecayMismatch
            (Measure.map
              (actualTwoMassChildFrequencyChart
                fixed site₁ site₂ parent child) iidMassPairLaw)
            (absoluteMismatchSublevel delta)).toReal :=
  exists_positive_actualTwoMass_childRepeated_linearSmallBallLower
    fixed site₁ site₂ parent child hpatch hpatchSupport hderivative
      hinjective hdetUpper hdet hchild hchildPos hchildFinite hradius
      hrectangle

#print axioms actualTwoMass_childRepeated_localLinearSmallBall

end

end ArchonPhysicsConsumers.Thermalization
