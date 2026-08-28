import ArchonPhysics.ComplexFourierBranchAmplitude

/-!
# Consumer: complex Fourier oscillator branches
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.ComplexFourierBranchAmplitude
open ArchonPhysics.FinitePhaseMonomials

noncomputable section

theorem problem_complex_fourier_branch_reconstruction
    {omega : Real} (homega : 0 < omega) (Q P : Complex) :
    Q =
      (complexFourierBranchAmplitude omega .phase Q P +
        complexFourierBranchAmplitude omega .conjugate Q P) /
          Real.sqrt (2 * omega) :=
  coordinate_eq_branch_sum_div_sqrt homega Q P

theorem problem_complex_fourier_interaction_branch_derivative
    {omega : Real} (homega : 0 < omega) (sign : PhaseSign)
    {Q P R : Real -> Complex} {time : Real}
    (hQ : HasDerivAt Q (P time) time)
    (hP : HasDerivAt P
      (-(omega ^ 2 : Real) * Q time + R time) time) :
    HasDerivAt
      (fun s => complexFourierInteractionBranch omega sign Q P s)
      (ArchonPhysics.PhaseRenormalization.phaseFactor
          (phaseSignReal sign * omega * time) *
        complexFourierBranchSource omega sign (R time)) time :=
  hasDerivAt_complexFourierInteractionBranch homega sign hQ hP

#print axioms problem_complex_fourier_branch_reconstruction
#print axioms problem_complex_fourier_interaction_branch_derivative

end

end ArchonPhysicsConsumers.Thermalization
