import ArchonPhysics.FrozenAndersonFiniteProductIccWegner

/-!
# Consumer: closed-interval frozen iid finite-volume Wegner bound

This consumer records the exact no-axiom endpoint proved by the core module.
For a finite real Hermitian background with iid `Uniform[4/5,6/5]`
diagonal masses and nonzero coupling, the expected rank of the genuine
Hermitian idempotent spectral projector on the closed interval `[a,b]` is at
most `(n+1) * (5 / (2 * |lambda|)) * (b-a)`.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FrozenAndersonFiniteProductSmoothedTraceWegner
open ArchonPhysics.FrozenAndersonFiniteProductIccWegner
open MeasureTheory

noncomputable section

/-- Exact closed-endpoint finite-volume Wegner estimate for the canonical
frozen iid Anderson diagonal. -/
theorem frozen_iid_uniform_finiteAnderson_Icc_spectralProjector_rank_le
    {n : Nat}
    (background : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (hbackground : background.IsHermitian)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (a b : Real) (hab : a <= b) :
    integral (canonicalFiniteIIDMassLaw (n + 1))
        (fun mass => ((finiteAndersonIccSpectralProjector
          background hbackground lambda a b mass).rank : Real)) <=
      (n + 1 : Real) * ((5 / (2 * |lambda|)) * (b - a)) :=
  integral_finiteAndersonIccSpectralProjector_rank_le
    background hbackground lambda hlambda a b hab

#print axioms finiteAndersonIccSpectralProjector_rank
#print axioms integral_finiteAndersonIccEigenvalueCount_le
#print axioms frozen_iid_uniform_finiteAnderson_Icc_spectralProjector_rank_le

end

end ArchonPhysicsConsumers.Thermalization
