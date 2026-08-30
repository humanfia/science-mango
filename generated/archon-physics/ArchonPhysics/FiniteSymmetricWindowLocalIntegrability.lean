import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Local integrability from symmetric finite-window bounds

Integrability on every symmetric integer window implies local integrability
on the whole real time axis.  The almost-everywhere version packages the
countable intersection over those windows.  This is a measure-theoretic
upgrade only: it does not assert global-in-time integrability or any bound
uniform in the window size.
-/

namespace ArchonPhysics.FiniteSymmetricWindowLocalIntegrability

open Set
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]

/-- Integrability on every symmetric integer window gives local
integrability on all of real time. -/
theorem locallyIntegrable_of_integrable_symmetric_natWindows
    {f : Real -> E}
    (hwindow : forall n : Nat,
      Integrable f (volume.restrict
        (Icc (-(n : Real)) (n : Real)))) :
    LocallyIntegrable f volume := by
  intro time
  obtain ⟨n, hn⟩ := exists_nat_gt |time|
  refine ⟨Icc (-(n : Real)) (n : Real), Icc_mem_nhds ?_ ?_, ?_⟩
  · exact (neg_lt_neg hn).trans_le (neg_abs_le time)
  · exact (le_abs_self time).trans_lt hn
  · exact hwindow n

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- If every symmetric integer-window time section is integrable almost
surely, then almost every complete time section is locally integrable. -/
theorem ae_locallyIntegrable_of_ae_integrable_symmetric_natWindows
    (f : Omega -> Real -> E)
    (hwindow : forall n : Nat,
      ∀ᵐ omega ∂mu,
        Integrable (f omega) (volume.restrict
          (Icc (-(n : Real)) (n : Real)))) :
    ∀ᵐ omega ∂mu, LocallyIntegrable (f omega) volume := by
  filter_upwards [ae_all_iff.mpr hwindow] with omega homega
  exact locallyIntegrable_of_integrable_symmetric_natWindows homega

end ArchonPhysics.FiniteSymmetricWindowLocalIntegrability
