import ArchonPhysics.AcousticVertexScaling

/-!
# Cubic vertex bounds at the acoustic edge

This module turns the exact one-leg identities from
`AcousticVertexScaling` into a three-leg estimate.  The proof is a finite
Cauchy--Schwarz argument and therefore applies to every positive mass
realization, without a thermodynamic limit or a probabilistic assumption.

For three positive-frequency modes, the squared normalized cubic vertex is
bounded by `omega_0 * omega_1 * omega_2 / 8`.  Thus a soft external leg makes
the vertex vanish at least linearly in that frequency.  This is only the
vertex half of infrared control: no claim is made that the resonant-state
density stays bounded or that the collision network is coercive.
-/

namespace ArchonPhysics.CubicVertexInfraredBound

open ArchonPhysics
open HarmonicModes
open ModeCoupling
open ModalPhaseMismatch
open NormalizedModeCoupling
open AcousticVertexScaling

noncomputable section

/-- One bond leg including the positive-frequency amplitude normalization. -/
def normalizedBondLeg {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (j k : Lattice.Site N) : Real :=
  bondModeCoefficient m j k * modeAmplitudeNormalization m k

/-- A finite three-factor Holder bound, proved from squared Cauchy--Schwarz. -/
theorem tripleProductSum_sq_le {ι : Type*} [Fintype ι]
    (a b c : ι -> Real) :
    (∑ i, a i * b i * c i) ^ 2 <=
      (∑ i, a i ^ 2) * (∑ i, b i ^ 2) * (∑ i, c i ^ 2) := by
  classical
  have hbc : (∑ i, (b i * c i) ^ 2) <=
      (∑ i, b i ^ 2) * (∑ i, c i ^ 2) := by
    calc
      (∑ i, (b i * c i) ^ 2) =
          ∑ i, b i ^ 2 * c i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ <= ∑ i, b i ^ 2 * (∑ j, c j ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun j _ => sq_nonneg (c j))
            (Finset.mem_univ i))
          (sq_nonneg (b i))
      _ = (∑ i, b i ^ 2) * (∑ i, c i ^ 2) := by
        rw [Finset.sum_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a
    (fun i => b i * c i)
  calc
    (∑ i, a i * b i * c i) ^ 2 =
        (∑ i, a i * (b i * c i)) ^ 2 := by
      congr 2
      funext i
      ring
    _ <= (∑ i, a i ^ 2) * (∑ i, (b i * c i) ^ 2) := hcs
    _ <= (∑ i, a i ^ 2) *
        ((∑ i, b i ^ 2) * (∑ i, c i ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hbc
        (Finset.sum_nonneg fun i _ => sq_nonneg (a i))
    _ = (∑ i, a i ^ 2) * (∑ i, b i ^ 2) *
        (∑ i, c i ^ 2) := by ring

/-- The raw cubic tensor is the bondwise product of its three legs. -/
theorem interactionTensor_three_eq_sum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin 3 -> Lattice.Site N) :
    interactionTensor m 3 modes =
      ∑ j, bondModeCoefficient m j (modes 0) *
        bondModeCoefficient m j (modes 1) *
        bondModeCoefficient m j (modes 2) := by
  unfold interactionTensor
  apply Finset.sum_congr rfl
  intro j hj
  rw [Fin.prod_univ_three]

/-- The normalized cubic vertex is the bondwise product of normalized legs. -/
theorem normalizedInteractionVertex_three_eq_sum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin 3 -> Lattice.Site N) :
    normalizedInteractionVertex m modes =
      ∑ j, normalizedBondLeg m j (modes 0) *
        normalizedBondLeg m j (modes 1) *
        normalizedBondLeg m j (modes 2) := by
  unfold normalizedInteractionVertex interactionTensor normalizedBondLeg
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Fin.prod_univ_three]
  ring

/-- The raw cubic coupling is bounded by the product of squared frequencies. -/
theorem interactionTensor_three_sq_le {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin 3 -> Lattice.Site N) :
    (interactionTensor m 3 modes) ^ 2 <=
      modeFrequencySq m (modes 0) * modeFrequencySq m (modes 1) *
        modeFrequencySq m (modes 2) := by
  rw [interactionTensor_three_eq_sum]
  calc
    (∑ j, bondModeCoefficient m j (modes 0) *
        bondModeCoefficient m j (modes 1) *
        bondModeCoefficient m j (modes 2)) ^ 2 <=
      (∑ j, bondModeCoefficient m j (modes 0) ^ 2) *
        (∑ j, bondModeCoefficient m j (modes 1) ^ 2) *
        (∑ j, bondModeCoefficient m j (modes 2) ^ 2) :=
      tripleProductSum_sq_le _ _ _
    _ = modeFrequencySq m (modes 0) * modeFrequencySq m (modes 1) *
        modeFrequencySq m (modes 2) := by
      rw [sum_sq_bondModeCoefficient, sum_sq_bondModeCoefficient,
        sum_sq_bondModeCoefficient]

/-- Exact acoustic upper bound for the squared normalized cubic vertex. -/
theorem normalizedInteractionVertex_three_sq_le {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin 3 -> Lattice.Site N)
    (hpositive : PositiveModeTuple m modes) :
    (normalizedInteractionVertex m modes) ^ 2 <=
      modeFrequency m (modes 0) * modeFrequency m (modes 1) *
        modeFrequency m (modes 2) / 8 := by
  rw [normalizedInteractionVertex_three_eq_sum]
  calc
    (∑ j, normalizedBondLeg m j (modes 0) *
        normalizedBondLeg m j (modes 1) *
        normalizedBondLeg m j (modes 2)) ^ 2 <=
      (∑ j, normalizedBondLeg m j (modes 0) ^ 2) *
        (∑ j, normalizedBondLeg m j (modes 1) ^ 2) *
        (∑ j, normalizedBondLeg m j (modes 2) ^ 2) :=
      tripleProductSum_sq_le _ _ _
    _ = (modeFrequency m (modes 0) / 2) *
        (modeFrequency m (modes 1) / 2) *
        (modeFrequency m (modes 2) / 2) := by
      unfold normalizedBondLeg
      rw [sum_sq_normalizedBondLeg _ _ (hpositive 0),
        sum_sq_normalizedBondLeg _ _ (hpositive 1),
        sum_sq_normalizedBondLeg _ _ (hpositive 2)]
    _ = modeFrequency m (modes 0) * modeFrequency m (modes 1) *
        modeFrequency m (modes 2) / 8 := by ring

/-- Collision-weight form of the same exact acoustic bound. -/
theorem normalizedInteractionWeight_three_le {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin 3 -> Lattice.Site N)
    (hpositive : PositiveModeTuple m modes) :
    normalizedInteractionWeight m modes <=
      modeFrequency m (modes 0) * modeFrequency m (modes 1) *
        modeFrequency m (modes 2) / 8 := by
  rw [<- normalizedInteractionVertex_sq]
  exact normalizedInteractionVertex_three_sq_le m modes hpositive

end

end ArchonPhysics.CubicVertexInfraredBound
