import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Uniform convergence on compact sets from a common Lipschitz bound

A uniformly Lipschitz family is uniformly equicontinuous.  On a compact
domain, Ascoli identifies pointwise convergence on that family with uniform
convergence.  This file packages the specialization to real arguments and
complex values.
-/

namespace ArchonPhysics.LipschitzPointwiseCompactUniform

open Filter Set Topology

/-- A common Lipschitz constant and pointwise convergence imply uniform
convergence on every compact subset of `Real`. -/
theorem tendstoUniformlyOn_of_lipschitzWith_of_pointwise
    (F : Nat -> Real -> Complex) (f : Real -> Complex) (K : NNReal)
    (hF : forall n, LipschitzWith K (F n))
    (hpointwise : forall t,
      Tendsto (fun n => F n t) atTop (nhds (f t)))
    {S : Set Real} (hS : IsCompact S) :
    TendstoUniformlyOn F f atTop S := by
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have huniform : UniformEquicontinuous F :=
    LipschitzWith.uniformEquicontinuous F K hF
  have hequicontinuous : Equicontinuous (S.domRestrict ∘ F) := by
    rw [equicontinuous_restrict_iff]
    exact huniform.equicontinuous.equicontinuousOn S
  have hpointwiseRestricted :
      Tendsto (S.domRestrict ∘ F) atTop (nhds (S.domRestrict f)) := by
    rw [tendsto_pi_nhds]
    intro t
    simpa [Function.comp_def] using hpointwise t
  have huniformFun :
      Tendsto (UniformFun.ofFun ∘ (S.domRestrict ∘ F)) atTop
        (nhds (UniformFun.ofFun (S.domRestrict f))) :=
    (hequicontinuous.tendsto_uniformFun_iff_pi atTop
      (S.domRestrict f)).2 hpointwiseRestricted
  rw [tendstoUniformlyOn_iff_restrict]
  simpa [Function.comp_def] using
    (UniformFun.tendsto_iff_tendstoUniformly.mp huniformFun)

/-- Existential form matching applications where only the existence of a
common Lipschitz constant is exposed. -/
theorem tendstoUniformlyOn_of_exists_lipschitzWith_of_pointwise
    (F : Nat -> Real -> Complex) (f : Real -> Complex)
    (hF : exists K : NNReal, forall n, LipschitzWith K (F n))
    (hpointwise : forall t,
      Tendsto (fun n => F n t) atTop (nhds (f t)))
    {S : Set Real} (hS : IsCompact S) :
    TendstoUniformlyOn F f atTop S := by
  obtain ⟨K, hK⟩ := hF
  exact tendstoUniformlyOn_of_lipschitzWith_of_pointwise
    F f K hK hpointwise hS

end ArchonPhysics.LipschitzPointwiseCompactUniform
