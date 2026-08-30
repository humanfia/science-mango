import ArchonPhysics.FiniteDuhamelPhaseAverage
import Mathlib.Tactic.FinCases

/-!
# Pairwise phase decoherence does not control a coherent triad

This finite Haar example is a guardrail for the random-phase part of the
Hamiltonian-to-kinetic argument.  On two independent base phases, define

`z₀ = exp(i θ₀)`, `z₁ = exp(i θ₁)`, and `z₂ = exp(i (θ₀ + θ₁))`.

The three character charges are pairwise distinct, so every off-diagonal
two-point covariance `E[zᵢ conj(zⱼ)]` vanishes.  Nevertheless
`z₀ z₁ conj(z₂) = 1` pointwise, and its expectation is one.  Thus a
two-point decoherence estimate alone cannot replace the arbitrary-order
phase-selection / connected-diagram estimates required by a wave-kinetic
limit.

This is a static probability example.  It makes no positive-time FPUT claim.
-/

namespace ArchonPhysics.PairwisePhaseDecoherenceInsufficient

open MeasureTheory
open UnitAddTorus
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The two independent base phases carry three distinct character charges:
the two coordinate charges and their sum. -/
def coherentTriadCharge : Fin 3 → Fin 2 → Int :=
  ![![1, 0], ![0, 1], ![1, 1]]

/-- The three unit-modulus phase variables in the counterexample. -/
def coherentTriadPhase (mode : Fin 3) (phase : UnitAddTorus (Fin 2)) : Complex :=
  mFourier (coherentTriadCharge mode) phase

/-- The three phase-character charges are pairwise distinct. -/
theorem coherentTriadCharge_injective : Function.Injective coherentTriadCharge := by
  intro first second heq
  fin_cases first <;> fin_cases second
  · rfl
  · have h := congrFun heq 0
    norm_num [coherentTriadCharge] at h
  · have h := congrFun heq 1
    norm_num [coherentTriadCharge] at h
  · have h := congrFun heq 0
    norm_num [coherentTriadCharge] at h
  · rfl
  · have h := congrFun heq 0
    norm_num [coherentTriadCharge] at h
  · have h := congrFun heq 1
    norm_num [coherentTriadCharge] at h
  · have h := congrFun heq 0
    norm_num [coherentTriadCharge] at h
  · rfl

/-- Every off-diagonal two-point covariance is exactly zero. -/
theorem integral_coherentTriadPhase_mul_star_eq_zero
    (first second : Fin 3) (hne : first ≠ second) :
    (∫ phase : UnitAddTorus (Fin 2),
      coherentTriadPhase first phase *
        starRingEnd Complex (coherentTriadPhase second phase)
      ∂finitePhaseHaarLaw (Fin 2)) = 0 := by
  simp only [coherentTriadPhase, mFourier_mul_star_mFourier]
  apply integral_mFourier_eq_zero
  intro hzero
  apply hne
  apply coherentTriadCharge_injective
  exact sub_eq_zero.mp hzero

/-- The charge of the third phase is the sum of the first two charges. -/
theorem coherentTriadCharge_two_eq_zero_add_one :
    coherentTriadCharge 2 = coherentTriadCharge 0 + coherentTriadCharge 1 := by
  decide

/-- Despite all pairwise off-diagonal covariances vanishing, the coherent
three-point moment is exactly one. -/
theorem integral_coherentTriad_threePoint_eq_one :
    (∫ phase : UnitAddTorus (Fin 2),
      coherentTriadPhase 0 phase * coherentTriadPhase 1 phase *
        starRingEnd Complex (coherentTriadPhase 2 phase)
      ∂finitePhaseHaarLaw (Fin 2)) = 1 := by
  have hpointwise : ∀ phase : UnitAddTorus (Fin 2),
      coherentTriadPhase 0 phase * coherentTriadPhase 1 phase *
          starRingEnd Complex (coherentTriadPhase 2 phase) =
        mFourier
          (coherentTriadCharge 0 + coherentTriadCharge 1 -
            coherentTriadCharge 2) phase := by
    intro phase
    unfold coherentTriadPhase
    rw [← mFourier_add, ← mFourier_neg, ← mFourier_add]
    rfl
  calc
    (∫ phase : UnitAddTorus (Fin 2),
        coherentTriadPhase 0 phase * coherentTriadPhase 1 phase *
          starRingEnd Complex (coherentTriadPhase 2 phase)
        ∂finitePhaseHaarLaw (Fin 2)) =
        ∫ phase : UnitAddTorus (Fin 2),
          mFourier
            (coherentTriadCharge 0 + coherentTriadCharge 1 -
              coherentTriadCharge 2) phase
          ∂finitePhaseHaarLaw (Fin 2) := by
      apply integral_congr_ae
      filter_upwards [] with phase
      exact hpointwise phase
    _ = 1 := by
      apply integral_mFourier_eq_one
      rw [coherentTriadCharge_two_eq_zero_add_one]
      simp

end

end ArchonPhysics.PairwisePhaseDecoherenceInsufficient
