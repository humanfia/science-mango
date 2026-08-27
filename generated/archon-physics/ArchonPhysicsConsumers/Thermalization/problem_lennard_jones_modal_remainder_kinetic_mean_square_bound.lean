import ArchonPhysics.LennardJonesModalRemainderKineticMeanSquareBound

/-!
# Consumer: kinetic-window mean-square LJ modal remainder
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesModalRemainderKineticMeanSquareBound

open Set
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.LennardJonesKineticTimeForceRemainder
open ArchonPhysics.LennardJonesModalRemainderKineticMeanSquareBound
open ArchonPhysics.LennardJonesModalRemainderMeanSquareBound

noncomputable section

theorem paperMassSupport_norm_integral_meanSquare_le_kinetic
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hmass : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    {depth r₀ g rho L amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 ≤ L) (hAmplitude : 0 ≤ amplitudeBound)
    (q : Real → HilbertConfiguration N)
    (hIntegrable : IntervalIntegrable
      (fun t => modalHigherResidualMeanSquare m depth r₀ g (q t))
      MeasureTheory.volume 0 (kineticWindowTime g L))
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |g * Lattice.forwardDifference (asConfiguration (q t)) i| ≤ rho * r₀)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |Lattice.forwardDifference (asConfiguration (q t)) i| ≤ amplitudeBound) :
    ‖∫ t in 0..kineticWindowTime g L,
        modalHigherResidualMeanSquare m depth r₀ g (q t)‖ ≤
      5 * kineticForceRemainderCoefficient r₀ rho amplitudeBound ^ 2 *
        L * g ^ 4 := by
  have h :=
    (intervalIntegrable_and_norm_integral_modalHigherResidualMeanSquare_le_kinetic
      m (4 / 5 : Real) (by norm_num) hmass hdepth hr₀ hg hrho0 hrho1 hL
        hAmplitude q hIntegrable htube hamplitude).2
  norm_num at h ⊢
  exact h

theorem paperMassSupport_abs_timeAverage_meanSquare_le_g_six
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hmass : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    {depth r₀ g rho L amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 < L) (hAmplitude : 0 ≤ amplitudeBound)
    (q : Real → HilbertConfiguration N)
    (hIntegrable : IntervalIntegrable
      (fun t => modalHigherResidualMeanSquare m depth r₀ g (q t))
      MeasureTheory.volume 0 (kineticWindowTime g L))
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |g * Lattice.forwardDifference (asConfiguration (q t)) i| ≤ rho * r₀)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |Lattice.forwardDifference (asConfiguration (q t)) i| ≤ amplitudeBound) :
    |kineticWindowModalHigherResidualMeanSquareAverage
        m depth r₀ g L q| ≤
      5 * kineticForceRemainderCoefficient r₀ rho amplitudeBound ^ 2 * g ^ 6 := by
  have h := abs_kineticWindowModalHigherResidualMeanSquareAverage_le_g_six
    m (4 / 5 : Real) (by norm_num) hmass hdepth hr₀ hg hrho0 hrho1 hL
      hAmplitude q hIntegrable htube hamplitude
  norm_num at h ⊢
  exact h

#print axioms paperMassSupport_norm_integral_meanSquare_le_kinetic
#print axioms paperMassSupport_abs_timeAverage_meanSquare_le_g_six
#print axioms intervalIntegrable_and_norm_integral_modalHigherResidualMeanSquare_le_kinetic
#print axioms abs_kineticWindowModalHigherResidualMeanSquareAverage_le_g_six

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesModalRemainderKineticMeanSquareBound
