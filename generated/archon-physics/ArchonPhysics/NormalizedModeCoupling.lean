import ArchonPhysics.ComplexModeAmplitude

/-!
# Positive-frequency normalization of finite mode couplings

The real-coordinate tensor in `ModeCoupling` is not yet the physical phonon
vertex.  With the complex-amplitude convention

`a = (omega * Q + i * P) / sqrt (2 * omega)`,

each modal coordinate contributes a factor `1 / sqrt (2 * omega)`.  This
module records that exact normalization and its squared magnitude.  A
different amplitude convention may multiply the vertex by a unit complex
phase; its squared magnitude is unchanged.

The translation zero mode is excluded from physical use by the explicit
`PositiveModeTuple` predicate.  Definitions remain total under Lean's
zero-inverse convention, but no theorem treats a zero-frequency factor as a
physical phonon mode.
-/

namespace ArchonPhysics.NormalizedModeCoupling

open ArchonPhysics
open ModeCoupling
open ModalPhaseMismatch

noncomputable section

/-- Every entry of a supplied mode tuple has strictly positive frequency. -/
def PositiveModeTuple {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Lattice.Site N) : Prop :=
  ∀ r, 0 < modeFrequency m (modes r)

/-- The coordinate-to-complex-amplitude normalization for one mode. -/
def modeAmplitudeNormalization {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N) : Real :=
  (Real.sqrt (2 * modeFrequency m k))⁻¹

/-- The normalized real vertex in the convention used by
`ComplexModeAmplitude`. -/
def normalizedInteractionVertex {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Lattice.Site N) : Real :=
  interactionTensor m n modes *
    ∏ r, modeAmplitudeNormalization m (modes r)

/-- Squared magnitude of the physical vertex.  This is the quantity entering
second-order collision weights. -/
def normalizedInteractionWeight {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Lattice.Site N) : Real :=
  (interactionTensor m n modes) ^ 2 *
    ∏ r, (2 * modeFrequency m (modes r))⁻¹

theorem modeAmplitudeNormalization_pos {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    (hfrequency : 0 < modeFrequency m k) :
    0 < modeAmplitudeNormalization m k := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (mul_pos zero_lt_two hfrequency))

theorem normalizedInteractionWeight_nonneg {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Lattice.Site N) :
    0 ≤ normalizedInteractionWeight m modes := by
  apply mul_nonneg (sq_nonneg _)
  apply Finset.prod_nonneg
  intro r hr
  exact inv_nonneg.mpr (mul_nonneg zero_le_two (modeFrequency_nonneg m _))

/-- Squaring the normalized real vertex gives the explicit product of inverse
frequencies. -/
theorem normalizedInteractionVertex_sq {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Lattice.Site N) :
    (normalizedInteractionVertex m modes) ^ 2 =
      normalizedInteractionWeight m modes := by
  unfold normalizedInteractionVertex normalizedInteractionWeight
  rw [mul_pow, ← Finset.prod_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  unfold modeAmplitudeNormalization
  rw [inv_pow, Real.sq_sqrt]
  exact mul_nonneg zero_le_two (modeFrequency_nonneg m _)

/-- The normalized vertex retains the permutation symmetry of the raw tensor. -/
theorem normalizedInteractionVertex_perm {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Lattice.Site N) (sigma : Equiv.Perm (Fin n)) :
    normalizedInteractionVertex m (modes ∘ sigma) =
      normalizedInteractionVertex m modes := by
  unfold normalizedInteractionVertex
  rw [interactionTensor_perm]
  congr 1
  exact Equiv.prod_comp sigma
    (fun r ↦ modeAmplitudeNormalization m (modes r))

/-- The squared physical weight is likewise permutation invariant. -/
theorem normalizedInteractionWeight_perm {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : Fin n → Lattice.Site N) (sigma : Equiv.Perm (Fin n)) :
    normalizedInteractionWeight m (modes ∘ sigma) =
      normalizedInteractionWeight m modes := by
  rw [← normalizedInteractionVertex_sq,
    normalizedInteractionVertex_perm, normalizedInteractionVertex_sq]

end

end ArchonPhysics.NormalizedModeCoupling
