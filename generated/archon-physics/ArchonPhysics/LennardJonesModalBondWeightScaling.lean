import ArchonPhysics.AcousticVertexScaling
import ArchonPhysics.LennardJonesModalRemainderKineticBound

/-!
# Volume scaling of the finite-mode LJ remainder coefficient

The `l1` bond weight of one normalized random-mass mode is bounded by
`sqrt(N)` times its harmonic frequency.  This follows from finite
Cauchy--Schwarz and the exact bond-leg `l2` identity.  It quantifies, rather
than hides, the finite-volume factor in the LJ kinetic-time remainder bound.

The estimate alone is not uniform in volume; further cancellation or the
normalization of the kinetic observable is still required in a joint
thermodynamic/weak-coupling limit.
-/

namespace ArchonPhysics.LennardJonesModalBondWeightScaling

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.AcousticVertexScaling
open ArchonPhysics.LennardJonesModalRemainderKineticBound
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling

noncomputable section

/-- Exact finite-volume Cauchy--Schwarz bound for the bond `l1` weight of one
normal mode. -/
theorem modalBondL1Weight_le_sqrt_card_mul_frequency
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N) :
    modalBondL1Weight m k ≤ Real.sqrt (N : Real) * modeFrequency m k := by
  classical
  calc
    modalBondL1Weight m k =
        ∑ i ∈ (Finset.univ : Finset (Lattice.Site N)),
          (1 : Real) * |bondModeCoefficient m i k| := by
      simp [modalBondL1Weight]
    _ ≤ Real.sqrt
          (∑ i ∈ (Finset.univ : Finset (Lattice.Site N)), (1 : Real) ^ 2) *
        Real.sqrt
          (∑ i ∈ (Finset.univ : Finset (Lattice.Site N)),
            |bondModeCoefficient m i k| ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun _ : Lattice.Site N => (1 : Real))
        (fun i => |bondModeCoefficient m i k|)
    _ = Real.sqrt (N : Real) * modeFrequency m k := by
      have habs :
          (∑ i : Lattice.Site N, |bondModeCoefficient m i k| ^ 2) =
            ∑ i : Lattice.Site N, (bondModeCoefficient m i k) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact sq_abs (bondModeCoefficient m i k)
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        one_pow, mul_one]
      rw [habs, sum_sq_bondModeCoefficient]
      simp [Lattice.Site, ZMod.card, modeFrequency]

/-- The squared bond `l1` weight is bounded by `N` times the squared mode
frequency. -/
theorem modalBondL1Weight_sq_le_card_mul_frequencySq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N) :
    modalBondL1Weight m k ^ 2 ≤
      (N : Real) * modeFrequencySq m k := by
  have h := modalBondL1Weight_le_sqrt_card_mul_frequency m k
  have hleft : 0 ≤ modalBondL1Weight m k := by
    unfold modalBondL1Weight
    positivity
  have hright : 0 ≤ Real.sqrt (N : Real) * modeFrequency m k :=
    mul_nonneg (Real.sqrt_nonneg _) (modeFrequency_nonneg m k)
  have hsquare := (sq_le_sq₀ hleft hright).2 h
  calc
    modalBondL1Weight m k ^ 2 ≤
        (Real.sqrt (N : Real) * modeFrequency m k) ^ 2 := hsquare
    _ = (N : Real) * modeFrequencySq m k := by
      rw [mul_pow, Real.sq_sqrt]
      · rw [modeFrequency_sq]
      · positivity

end

end ArchonPhysics.LennardJonesModalBondWeightScaling
