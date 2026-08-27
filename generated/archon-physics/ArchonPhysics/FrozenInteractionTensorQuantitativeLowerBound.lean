import ArchonPhysics.FrozenCollisionMassPositivityGeneralN

/-!
# Quantitative lower bounds for frozen three-wave interaction tensors

The local cubic witness used for qualitative nondegeneracy has an exact
cubic bond sum `-6` and squared Euclidean norm `5` at every size `N ≥ 3`.
Cauchy--Schwarz applied to its exact modal expansion gives a lower bound on
the full Hilbert--Schmidt square of the physical three-wave tensor.  Parseval
then replaces the witness modal energy by a coordinatewise mass upper bound.

The full tensor-square bound is independent of the number of sites.  When a
single tensor entry is extracted by a finite maximum argument, the expected
factor `N^3` appears because there are `N^3` ordered physical triples.  No
resonance, random limit, or relaxation statement is used.
-/

namespace ArchonPhysics.FrozenInteractionTensorQuantitativeLowerBound

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FrozenCollisionMassPositivity
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModeCoupling
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- At three sites, the generic local witness is exactly the previously
verified explicit witness. -/
theorem cubicWitnessConfiguration_three_eq :
    cubicWitnessConfiguration 3 = threeSiteCubicWitness := by
  funext i
  obtain ⟨k, rfl⟩ := (ZMod.finEquiv 3).surjective i
  fin_cases k <;>
    norm_num [cubicWitnessConfiguration, threeSiteCubicWitness] <;>
    decide

/-- The same local witness has cubic forward-difference sum `-6` for every
periodic size at least three. -/
theorem cubicWitnessConfiguration_sum_forwardDifference_cube_of_three_le
    {N : Nat} [NeZero N] (hN : 3 ≤ N) :
    (∑ i : Lattice.Site N,
      (Lattice.forwardDifference (cubicWitnessConfiguration N) i) ^ 3) = -6 := by
  rcases eq_or_lt_of_le hN with hEq | hLt
  · subst N
    rw [cubicWitnessConfiguration_three_eq]
    exact threeSiteCubicWitness_sum_forwardDifference_cube
  · exact cubicWitnessConfiguration_sum_forwardDifference_cube (by omega)

/-- The local witness has exact squared Euclidean norm `1^2 + 2^2 = 5`. -/
theorem sum_sq_cubicWitnessConfiguration
    {N : Nat} [NeZero N] (hN : 3 ≤ N) :
    (∑ i : Lattice.Site N, cubicWitnessConfiguration N i ^ 2) = 5 := by
  have h12 : (1 : ZMod N) ≠ 2 := by
    intro h
    have hcast : ((1 : Nat) : ZMod N) = ((2 : Nat) : ZMod N) := by
      simpa using h
    have hmod := (ZMod.natCast_eq_natCast_iff 1 2 N).mp hcast
    have := hmod.eq_of_lt_of_lt (by omega) (by omega)
    omega
  classical
  calc
    _ = ∑ i : ZMod N,
        ((if i = 1 then (1 : Real) else 0) +
          (if i = 2 then 4 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi1 : i = 1
      · subst i
        simp [cubicWitnessConfiguration, h12]
      by_cases hi2 : i = 2
      · subst i
        norm_num [cubicWitnessConfiguration, Ne.symm h12]
      · simp [cubicWitnessConfiguration, hi1, hi2]
    _ = 5 := by
      rw [Finset.sum_add_distrib]
      norm_num [Finset.sum_ite_eq']

/-- Summing the square of a three-factor product over all tuples factorizes
as the cube of the one-leg square sum. -/
theorem sum_sq_threeFactorProduct_eq_cube
    {K : Type*} [Fintype K] (a : K → Real) :
    (∑ modes : Fin 3 → K, (∏ r, a (modes r)) ^ 2) =
      (∑ k, a k ^ 2) ^ 3 := by
  calc
    _ = ∑ modes : Fin 3 → K, ∏ r, a (modes r) ^ 2 := by
      apply Finset.sum_congr rfl
      intro modes _hmodes
      rw [Finset.prod_pow]
    _ = ∏ _r : Fin 3, ∑ k, a k ^ 2 := by
      exact (Fintype.prod_sum (fun _r k ↦ a k ^ 2)).symm
    _ = (∑ k, a k ^ 2) ^ 3 := by
      rw [Fin.prod_univ_three]
      ring

/-- Quantitative modal-completeness statement for any configuration whose
cubic bond sum is `-6`. -/
theorem thirtySix_le_tensorSquareSum_mul_modalEnergyCube_of_cubicSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : Lattice.Configuration N)
    (hcubic : (∑ i : Lattice.Site N,
      (Lattice.forwardDifference q i) ^ 3) = -6) :
    36 ≤
      (∑ modes : Fin 3 → Lattice.Site N,
        (interactionTensor m 3 modes) ^ 2) *
      (∑ k, (modalCoordinates m
        (sqrtMassTransform m (WithLp.toLp 2 q)) k) ^ 2) ^ 3 := by
  let qHilbert : HilbertConfiguration N := WithLp.toLp 2 q
  let amplitude : WeightedConfiguration N :=
    modalCoordinates m (sqrtMassTransform m qHilbert)
  have hexpansion := sum_forwardDifference_pow_eq_interactionTensor
    (n := 3) m amplitude
  have hreconstruction : physicalReconstruction m amplitude = q := by
    change physicalReconstruction m
      (modalCoordinates m (sqrtMassTransform m qHilbert)) = q
    exact (physicalReconstruction_modalCoordinates_sqrtMassTransform
      m qHilbert).trans (by rfl)
  rw [hreconstruction, hcubic] at hexpansion
  have hcauchy :
      (∑ modes : Fin 3 → Lattice.Site N,
        interactionTensor m 3 modes * ∏ r, amplitude (modes r)) ^ 2 ≤
      (∑ modes : Fin 3 → Lattice.Site N,
        (interactionTensor m 3 modes) ^ 2) *
      (∑ modes : Fin 3 → Lattice.Site N,
        (∏ r, amplitude (modes r)) ^ 2) := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun modes : Fin 3 → Lattice.Site N ↦ interactionTensor m 3 modes)
      (fun modes ↦ ∏ r, amplitude (modes r)))
  rw [sum_sq_threeFactorProduct_eq_cube amplitude] at hcauchy
  change 36 ≤
    (∑ modes : Fin 3 → Lattice.Site N,
      (interactionTensor m 3 modes) ^ 2) *
    (∑ k, amplitude k ^ 2) ^ 3
  calc
    36 = (-6 : Real) ^ 2 := by norm_num
    _ = (∑ modes : Fin 3 → Lattice.Site N,
        interactionTensor m 3 modes * ∏ r, amplitude (modes r)) ^ 2 := by
      rw [← hexpansion]
    _ ≤ _ := hcauchy

/-- Parseval bounds the modal energy of a norm-five witness by five times a
coordinatewise mass upper bound. -/
theorem modalEnergy_le_five_mul_massUpper_of_witnessNorm
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : Lattice.Configuration N)
    (hqnorm : (∑ i : Lattice.Site N, q i ^ 2) = 5)
    (mUpper : Real) (hmUpper : ∀ i, m.mass i ≤ mUpper) :
    (∑ k, (modalCoordinates m
      (sqrtMassTransform m (WithLp.toLp 2 q)) k) ^ 2) ≤ 5 * mUpper := by
  rw [sum_sq_modalCoordinates, EuclideanSpace.real_norm_sq_eq]
  simp only [sqrtMassTransform_apply, mul_pow,
    Real.sq_sqrt (m.mass_pos _).le]
  calc
    (∑ i, m.mass i * q i ^ 2) ≤ ∑ i, mUpper * q i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_right (hmUpper i) (sq_nonneg (q i))
    _ = mUpper * ∑ i, q i ^ 2 := by rw [Finset.mul_sum]
    _ = 5 * mUpper := by rw [hqnorm]; ring

/-- The full physical three-wave tensor square obeys an `N`-independent
multiplicative lower bound under a common mass upper bound. -/
theorem thirtySix_le_tensorSquareSum_mul_massUpperCube
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hN : 3 ≤ N) (mUpper : Real) (hmUpper : ∀ i, m.mass i ≤ mUpper) :
    36 ≤
      (∑ modes : Fin 3 → Lattice.Site N,
        (interactionTensor m 3 modes) ^ 2) * (5 * mUpper) ^ 3 := by
  have hcauchy :=
    thirtySix_le_tensorSquareSum_mul_modalEnergyCube_of_cubicSum
      m (cubicWitnessConfiguration N)
        (cubicWitnessConfiguration_sum_forwardDifference_cube_of_three_le hN)
  have henergy := modalEnergy_le_five_mul_massUpper_of_witnessNorm
    m (cubicWitnessConfiguration N)
      (sum_sq_cubicWitnessConfiguration hN) mUpper hmUpper
  have henergyNonneg :
      0 ≤ ∑ k, (modalCoordinates m
        (sqrtMassTransform m
          (WithLp.toLp 2 (cubicWitnessConfiguration N))) k) ^ 2 :=
    Finset.sum_nonneg fun k _hk ↦ sq_nonneg _
  have htensorNonneg :
      0 ≤ ∑ modes : Fin 3 → Lattice.Site N,
        (interactionTensor m 3 modes) ^ 2 :=
    Finset.sum_nonneg fun modes _hmodes ↦ sq_nonneg _
  exact hcauchy.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ henergyNonneg henergy 3) htensorNonneg)

/-- Consequently at least one physical tensor entry has an explicit square
lower bound.  The `N^3` denominator is the cost of selecting one entry among
all ordered physical triples. -/
theorem exists_interactionTensor_sq_ge_explicit
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hN : 3 ≤ N) (mUpper : Real) (hmUpper : ∀ i, m.mass i ≤ mUpper) :
    ∃ modes : Fin 3 → Lattice.Site N,
      36 / (((N : Real) ^ 3) * (5 * mUpper) ^ 3) ≤
        (interactionTensor m 3 modes) ^ 2 := by
  let tensorSq : (Fin 3 → Lattice.Site N) → Real := fun modes ↦
    (interactionTensor m 3 modes) ^ 2
  obtain ⟨modes, _hmodes, hmax⟩ := Finset.exists_max_image
    Finset.univ tensorSq Finset.univ_nonempty
  have hsumLe := Finset.sum_le_card_nsmul Finset.univ tensorSq
    (tensorSq modes) hmax
  have hcard : Fintype.card (Fin 3 → Lattice.Site N) = N ^ 3 := by
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hsumLeReal :
      (∑ tuple : Fin 3 → Lattice.Site N,
        (interactionTensor m 3 tuple) ^ 2) ≤
      (N : Real) ^ 3 * (interactionTensor m 3 modes) ^ 2 := by
    simpa [tensorSq, hcard, nsmul_eq_mul] using hsumLe
  have hmUpperPos : 0 < mUpper :=
    (m.mass_pos 0).trans_le (hmUpper 0)
  have hNPos : 0 < (N : Real) := by positivity
  have hdenomPos :
      0 < ((N : Real) ^ 3) * (5 * mUpper) ^ 3 := by positivity
  refine ⟨modes, (div_le_iff₀ hdenomPos).2 ?_⟩
  have hbase := thirtySix_le_tensorSquareSum_mul_massUpperCube
    m hN mUpper hmUpper
  have hmassCubeNonneg : 0 ≤ (5 * mUpper) ^ 3 := by positivity
  have hupper := mul_le_mul_of_nonneg_right hsumLeReal hmassCubeNonneg
  calc
    36 ≤
        (∑ tuple : Fin 3 → Lattice.Site N,
          (interactionTensor m 3 tuple) ^ 2) * (5 * mUpper) ^ 3 := hbase
    _ ≤ ((N : Real) ^ 3 * (interactionTensor m 3 modes) ^ 2) *
        (5 * mUpper) ^ 3 := hupper
    _ = (interactionTensor m 3 modes) ^ 2 *
        ((N : Real) ^ 3 * (5 * mUpper) ^ 3) := by ring

end

end ArchonPhysics.FrozenInteractionTensorQuantitativeLowerBound
