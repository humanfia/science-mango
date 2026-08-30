import ArchonPhysics.FrozenAndersonFiniteProductSmoothedTraceWegner

/-!
# Consumer: finite-product eta-smoothed Wegner bound

This consumer records the completed no-axiom finite-volume endpoint for the
canonical iid `Uniform[4/5, 6/5]` Anderson diagonal.  Coordinate Fubini
reconstructs the full product expectation from the sharp one-site Poisson
estimate, and the diagonal Green sum gives the eta-smoothed trace bound.

The result stops deliberately before an unsmoothed spectral-projector
estimate: no Stone limit or `eta -> 0` premise is introduced here.
-/

namespace ArchonPhysicsConsumers.Thermalization
namespace ProblemFrozenAndersonFiniteProductSmoothedTraceWegner

open ArchonPhysics
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.FrozenAndersonFiniteProductSmoothedTraceWegner
open MeasureTheory
open scoped BigOperators Matrix

noncomputable section

/-- Reusable explicit coordinate-conditioning theorem for a canonical finite
product probability law. -/
theorem problem_frozenAnderson_finitePi_coordinate_conditioning
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    {n : Nat} (i : Fin (n + 1))
    {f : (Fin (n + 1) -> alpha) -> Real} {C : Real}
    (hf : Measurable f) (hC : 0 <= C)
    (hnonneg : forall x, 0 <= f x)
    (hsection_integrable : forall rest : Fin n -> alpha,
      Integrable
        (fun x => f ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => alpha) i).symm (x, rest))) mu)
    (hsection_le : forall rest : Fin n -> alpha,
      (integral mu fun x => f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => alpha) i).symm (x, rest))) <= C) :
    Integrable f (Measure.pi fun _ : Fin (n + 1) => mu) /\
      (integral (Measure.pi fun _ : Fin (n + 1) => mu) f <= C) :=
  finitePi_coordinate_integrable_and_integral_le
    mu i hf hC hnonneg hsection_integrable hsection_le

/-- Sharp local Green estimate under the complete canonical iid finite mass
law, with every complementary coordinate integrated out. -/
theorem problem_frozenAnderson_uniform_fullProduct_localGreen
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (i : Fin (n + 1)) (z : Complex) (hz : 0 < z.im) :
    Integrable
        (fun mass => -(finiteAndersonLocalGreen
          background lambda mass i z).im)
        (canonicalFiniteIIDMassLaw (n + 1)) /\
      (integral (canonicalFiniteIIDMassLaw (n + 1))
        (fun mass => -(finiteAndersonLocalGreen
          background lambda mass i z).im) <=
        (5 / 2 : Real) * |lambda|⁻¹ * Real.pi) :=
  integrable_and_integral_finiteAndersonLocalGreen_neg_im_canonicalFiniteIIDMassLaw
    background hbackground lambda hlambda i z hz

/-- Full finite-volume no-axiom eta-smoothed trace Wegner theorem for iid
`Uniform[4/5, 6/5]` Anderson masses. -/
theorem problem_frozenAnderson_uniform_etaSmoothedTrace
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (energy eta : Real) (heta : 0 < eta) :
    Integrable (finiteAndersonEtaSmoothedTrace
        background lambda energy eta)
        (canonicalFiniteIIDMassLaw (n + 1)) /\
      (integral (canonicalFiniteIIDMassLaw (n + 1))
          (finiteAndersonEtaSmoothedTrace background lambda energy eta) <=
        (n + 1 : Real) *
          ((5 / 2 : Real) * |lambda|⁻¹ * Real.pi)) := by
  exact ⟨
    integrable_finiteAndersonEtaSmoothedTrace_canonicalFiniteIIDMassLaw
      background hbackground lambda hlambda energy eta heta,
    integral_finiteAndersonEtaSmoothedTrace_canonicalFiniteIIDMassLaw_le
      background hbackground lambda hlambda energy eta heta⟩

#print axioms problem_frozenAnderson_finitePi_coordinate_conditioning
#print axioms problem_frozenAnderson_uniform_fullProduct_localGreen
#print axioms problem_frozenAnderson_uniform_etaSmoothedTrace

end

end ProblemFrozenAndersonFiniteProductSmoothedTraceWegner
end ArchonPhysicsConsumers.Thermalization
