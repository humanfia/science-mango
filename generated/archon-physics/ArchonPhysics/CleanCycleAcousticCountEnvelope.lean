import ArchonPhysics.RandomMassAcousticCountingComparison
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Explicit clean-cycle acoustic counting

This file starts from the standard periodic difference matrix already used by
the random-mass harmonic model.  Complex additive characters of `ZMod N`
diagonalize its clean Gram matrix, with the complete multiplicity-labelled
spectrum

`4 * sin² (π j / N)`, `j = 0, ..., N - 1`.

The finite threshold count below retains multiplicities and explicitly keeps
the translation zero mode.  All statements are deterministic finite-volume
facts.  No random, density-of-states, localization, or thermodynamic-limit
claim is made.
-/

open scoped BigOperators ComplexConjugate

namespace ArchonPhysics.CleanCycleAcousticCountEnvelope

open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassAcousticCountingComparison
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

noncomputable section

/-- The additive-character basis of complex functions on the periodic cycle. -/
def cleanCycleFourierBasis (N : Nat) [NeZero N] :
    Module.Basis (Site N) Complex (Site N → Complex) :=
  (AddChar.complexBasis (Site N)).reindex
    (AddChar.zmodAddEquiv (n := N)).symm.toEquiv

@[simp] theorem cleanCycleFourierBasis_apply
    (N : Nat) [NeZero N] (j i : Site N) :
    cleanCycleFourierBasis N j i = AddChar.zmodAddEquiv j i := by
  simp [cleanCycleFourierBasis]

/-- Evaluation of a Fourier character on an integer representative. -/
theorem cleanCycleFourierBasis_apply_intCast
    (N : Nat) [NeZero N] (j : Site N) (x : Int) :
    cleanCycleFourierBasis N j (x : ZMod N) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((j.val : Real) * (x : Real) / (N : Real))) := by
  rw [cleanCycleFourierBasis_apply, AddChar.zmodAddEquiv_apply]
  change AddChar.toMonoidHomEquiv.symm
    (Circle.coeHom.comp (AddChar.zmod N j).toMonoidHom) (x : ZMod N) = _
  rw [AddChar.toMonoidHomEquiv_symm_apply]
  change (↑(AddChar.zmod N j (x : ZMod N)) : Complex) = _
  conv_lhs => rw [show j = ((j.val : Int) : ZMod N) by simp]
  rw [AddChar.zmod_intCast, Circle.coe_exp]
  congr 1
  push_cast
  ring

/-- The multiplicity-labelled clean-cycle eigenvalue at Fourier index `j`. -/
def cleanCycleModeEnergy (N : Nat) [NeZero N] (j : Site N) : Real :=
  4 * Real.sin (Real.pi * (j.val : Real) / (N : Real)) ^ 2

/-- The character shift multiplier is the real number
`4 sin²(π j/N)`. -/
theorem cleanCycleModeEnergy_fourier
    (N : Nat) [NeZero N] (j : ZMod N) :
    (cleanCycleModeEnergy N j : Complex) =
      2 - cleanCycleFourierBasis N j ((-1 : Int) : ZMod N) -
        cleanCycleFourierBasis N j ((1 : Int) : ZMod N) := by
  let a : Real := Real.pi * (j.val : Real) / (N : Real)
  have hneg : cleanCycleFourierBasis N j ((-1 : Int) : ZMod N) =
      Complex.exp ((-2 * a : Real) * Complex.I) := by
    rw [cleanCycleFourierBasis_apply_intCast N j (-1)]
    congr 1
    dsimp [a]
    push_cast
    norm_num
    ring
  have hpos : cleanCycleFourierBasis N j ((1 : Int) : ZMod N) =
      Complex.exp ((2 * a : Real) * Complex.I) := by
    rw [cleanCycleFourierBasis_apply_intCast N j 1]
    congr 1
    dsimp [a]
    push_cast
    norm_num
    ring
  rw [hneg, hpos, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, sub_zero]
    norm_num
    rw [Real.cos_two_mul']
    change 4 * Real.sin a ^ 2 =
      2 - (Real.cos a ^ 2 - Real.sin a ^ 2) -
        (Real.cos a ^ 2 - Real.sin a ^ 2)
    nlinarith [Real.sin_sq_add_cos_sq a]
  · simp only [Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, zero_add]
    norm_num

/-- Complexification of the forward difference acts by the same periodic
coordinate formula. -/
theorem differenceMatrix_map_mulVec {N : Nat} [NeZero N]
    (q : Site N → Complex) :
    Matrix.mulVec (differenceMatrix.map Complex.ofRealHom) q =
      fun i ↦ q (i + 1) - q i := by
  ext i
  simp only [Matrix.mulVec, differenceMatrix, dotProduct, Matrix.map_apply,
    map_sub, sub_mul]
  rw [Finset.sum_sub_distrib]
  simp

/-- Complexification of the transposed difference acts by the backward
difference. -/
theorem transposeDifferenceMatrix_map_mulVec {N : Nat} [NeZero N]
    (q : Site N → Complex) :
    Matrix.mulVec (Matrix.transpose (differenceMatrix.map Complex.ofRealHom)) q =
      fun i ↦ q (i - 1) - q i := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.map_apply, differenceMatrix, map_sub, sub_mul]
  rw [Finset.sum_sub_distrib]
  have hshift (j : Site N) : i = j + 1 ↔ j = i - 1 := by
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  simp_rw [hshift]
  simp

/-- Coordinate action of the complexified clean cycle Laplacian. -/
theorem cleanCycleHarmonicMatrix_map_mulVec {N : Nat} [NeZero N]
    (q : Site N → Complex) :
    Matrix.mulVec ((cleanCycleHarmonicMatrix N).map Complex.ofRealHom) q =
      fun i ↦ 2 * q i - q (i - 1) - q (i + 1) := by
  rw [cleanCycleHarmonicMatrix, Matrix.map_mul, Matrix.transpose_map,
    ← Matrix.mulVec_mulVec, differenceMatrix_map_mulVec,
    transposeDifferenceMatrix_map_mulVec]
  ext i
  ring_nf

/-- Every additive character is an eigenvector of the clean cycle Laplacian
with eigenvalue `cleanCycleModeEnergy`. -/
theorem cleanCycleFourierBasis_eigen {N : Nat} [NeZero N] (j : Site N) :
    Matrix.mulVec ((cleanCycleHarmonicMatrix N).map Complex.ofRealHom)
        (cleanCycleFourierBasis N j) =
      (cleanCycleModeEnergy N j : Complex) • cleanCycleFourierBasis N j := by
  rw [cleanCycleHarmonicMatrix_map_mulVec]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  have hminus : cleanCycleFourierBasis N j (i - 1) =
      cleanCycleFourierBasis N j i *
        cleanCycleFourierBasis N j ((-1 : Int) : ZMod N) := by
    rw [show i - 1 = i + ((-1 : Int) : ZMod N) by ring]
    simp only [cleanCycleFourierBasis_apply, AddChar.map_add_eq_mul]
  have hplus : cleanCycleFourierBasis N j (i + 1) =
      cleanCycleFourierBasis N j i *
        cleanCycleFourierBasis N j ((1 : Int) : ZMod N) := by
    rw [show i + 1 = i + ((1 : Int) : ZMod N) by norm_num]
    simp only [cleanCycleFourierBasis_apply, AddChar.map_add_eq_mul]
  rw [hminus, hplus, cleanCycleModeEnergy_fourier]
  ring

/-- Complexified clean-cycle linear operator. -/
def cleanCycleComplexLinear (N : Nat) [NeZero N] :
    (Site N → Complex) →ₗ[Complex] (Site N → Complex) :=
  Matrix.toLin' ((cleanCycleHarmonicMatrix N).map Complex.ofRealHom)

/-- The Fourier basis diagonalizes the full complexified clean operator. -/
theorem cleanCycleComplexLinear_toMatrix_fourier
    (N : Nat) [NeZero N] :
    LinearMap.toMatrix (cleanCycleFourierBasis N) (cleanCycleFourierBasis N)
        (cleanCycleComplexLinear N) =
      Matrix.diagonal (fun j ↦ (cleanCycleModeEnergy N j : Complex)) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  rw [show cleanCycleComplexLinear N (cleanCycleFourierBasis N j) =
      (cleanCycleModeEnergy N j : Complex) • cleanCycleFourierBasis N j by
        exact cleanCycleFourierBasis_eigen j]
  rw [(cleanCycleFourierBasis N).repr.map_smul,
    Module.Basis.repr_self]
  by_cases h : i = j
  · subst i
    simp
  · simp [h]


/-- Characteristic polynomial of the complexified clean cycle, written in
the Fourier basis. -/
theorem cleanCycleComplex_charpoly_eq_modeDiagonal
    (N : Nat) [NeZero N] :
    ((cleanCycleHarmonicMatrix N).map Complex.ofRealHom).charpoly =
      (Matrix.diagonal
        (fun j : Site N ↦ (cleanCycleModeEnergy N j : Complex))).charpoly := by
  calc
    ((cleanCycleHarmonicMatrix N).map Complex.ofRealHom).charpoly =
        (cleanCycleComplexLinear N).charpoly := by
      exact (Matrix.charpoly_toLin'
        ((cleanCycleHarmonicMatrix N).map Complex.ofRealHom)).symm
    _ = (LinearMap.toMatrix (cleanCycleFourierBasis N)
          (cleanCycleFourierBasis N) (cleanCycleComplexLinear N)).charpoly := by
      exact (LinearMap.charpoly_toMatrix (cleanCycleComplexLinear N)
        (cleanCycleFourierBasis N)).symm
    _ = (Matrix.diagonal
          (fun j : Site N ↦ (cleanCycleModeEnergy N j : Complex))).charpoly := by
      rw [cleanCycleComplexLinear_toMatrix_fourier]

/-- The real clean cycle has the same characteristic polynomial as the real
diagonal matrix of the explicit Fourier energies. -/
theorem cleanCycle_charpoly_eq_modeDiagonal
    (N : Nat) [NeZero N] :
    (cleanCycleHarmonicMatrix N).charpoly =
      (Matrix.diagonal
        (fun j : Site N ↦ cleanCycleModeEnergy N j)).charpoly := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
  have h := cleanCycleComplex_charpoly_eq_modeDiagonal N
  convert h using 1
  simp [Matrix.diagonal_map]

/-- Complete multiplicity-labelled characteristic polynomial formula for the
clean periodic cycle. -/
theorem cleanCycle_charpoly_formula (N : Nat) [NeZero N] :
    (cleanCycleHarmonicMatrix N).charpoly =
      ∏ j : Site N,
        (Polynomial.X - Polynomial.C (cleanCycleModeEnergy N j)) := by
  rw [cleanCycle_charpoly_eq_modeDiagonal, Matrix.charpoly_diagonal]

/-- The multiset of all Hermitian eigenvalues is exactly the multiset of
Fourier energies `4 sin²(πj/N)`. -/
theorem cleanCycle_eigenvalues_multiset_eq_modeEnergy
    (N : Nat) [NeZero N] :
    Multiset.map (cleanCycleHarmonicHermitian N).property.eigenvalues
        Finset.univ.val =
      Multiset.map (cleanCycleModeEnergy N) Finset.univ.val := by
  calc
    Multiset.map (cleanCycleHarmonicHermitian N).property.eigenvalues
        Finset.univ.val =
        (cleanCycleHarmonicMatrix N).charpoly.roots := by
      symm
      simpa [cleanCycleHarmonicHermitian] using
        (cleanCycleHarmonicHermitian N).property.roots_charpoly_eq_eigenvalues
    _ = (∏ j : Site N,
          (Polynomial.X - Polynomial.C (cleanCycleModeEnergy N j))).roots := by
      rw [cleanCycle_charpoly_formula]
    _ = Multiset.map (cleanCycleModeEnergy N) Finset.univ.val := by
      rw [Polynomial.roots_prod]
      · simp
      · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- Explicit Fourier indices below threshold `E`.  Multiplicity is retained;
the translation index `j = 0` is not removed. -/
def cleanCycleModeThresholdIndices
    (N : Nat) [NeZero N] (E : Real) : Finset (Site N) :=
  Finset.univ.filter fun j ↦ cleanCycleModeEnergy N j ≤ E

/-- Explicit clean-cycle sublevel count, including the zero mode whenever
`0 ≤ E`. -/
def cleanCycleModeThresholdCount
    (N : Nat) [NeZero N] (E : Real) : Nat :=
  (cleanCycleModeThresholdIndices N E).card

@[simp] theorem mem_cleanCycleModeThresholdIndices_iff
    (N : Nat) [NeZero N] (E : Real) (j : Site N) :
    j ∈ cleanCycleModeThresholdIndices N E ↔
      cleanCycleModeEnergy N j ≤ E := by
  simp [cleanCycleModeThresholdIndices]

/-- The ordered clean threshold count is unchanged by replacing the sorted
Hermitian eigenvalues with Mathlib's complete unsorted eigenvalue family. -/
theorem orderedEigenvalueThresholdCount_clean_eq_eigenvalueCount
    (N : Nat) [NeZero N] (E : Real) :
    orderedEigenvalueThresholdCount (cleanCycleHarmonicHermitian N) E =
      (Finset.univ.filter fun i : Site N ↦
        (cleanCycleHarmonicHermitian N).property.eigenvalues i ≤ E).card := by
  unfold orderedEigenvalueThresholdCount orderedEigenvalueThresholdIndices
  apply Finset.card_equiv
    (Fintype.equivOfCardEq (Fintype.card_fin _))
  intro k
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  unfold orderedEigenvalue Matrix.IsHermitian.eigenvalues
  rw [Equiv.symm_apply_apply]

/-- Exact bridge from the existing decreasing ordered spectral count to the
explicit multiplicity-labelled sine spectrum. -/
theorem orderedEigenvalueThresholdCount_clean_eq_modeThresholdCount
    (N : Nat) [NeZero N] (E : Real) :
    orderedEigenvalueThresholdCount (cleanCycleHarmonicHermitian N) E =
      cleanCycleModeThresholdCount N E := by
  rw [orderedEigenvalueThresholdCount_clean_eq_eigenvalueCount]
  unfold cleanCycleModeThresholdCount cleanCycleModeThresholdIndices
  have h := congrArg (fun s : Multiset Real ↦
    (s.filter fun x ↦ x ≤ E).card)
    (cleanCycle_eigenvalues_multiset_eq_modeEnergy N)
  simpa [Multiset.filter_map, Function.comp_def, Finset.card_def,
    Finset.filter_val] using h


/-- Distance of a Fourier label from the translation label around the cycle. -/
def cycleModeRadius (N : Nat) [NeZero N] (j : Site N) : Nat :=
  min j.val (N - j.val)

/-- Chord bound `sin x ≥ 2x/π` on the half-circle, in the normalization
used by the clean eigenvalues. -/
theorem sineChord_energy_lower {N d : Nat} [NeZero N]
    (h2d : 2 * d ≤ N) :
    16 * (d : Real) ^ 2 / (N : Real) ^ 2 ≤
      4 * Real.sin (Real.pi * (d : Real) / (N : Real)) ^ 2 := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hd : 0 ≤ (d : Real) := by positivity
  let a : Real := Real.pi * (d : Real) / (N : Real)
  have ha0 : 0 ≤ a := by positivity
  have h2dR : 2 * (d : Real) ≤ (N : Real) := by exact_mod_cast h2d
  have haHalf : a ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hN).2
    nlinarith [Real.pi_pos]
  have hlin : 2 / Real.pi * a ≤ Real.sin a :=
    Real.mul_le_sin ha0 haHalf
  have hsin0 : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha0
      (haHalf.trans (by nlinarith [Real.pi_pos]))
  have hleft0 : 0 ≤ 2 / Real.pi * a := by positivity
  have hsq : (2 / Real.pi * a) ^ 2 ≤ Real.sin a ^ 2 := by
    nlinarith
  calc
    16 * (d : Real) ^ 2 / (N : Real) ^ 2 =
        4 * (2 / Real.pi * a) ^ 2 := by
      dsimp [a]
      field_simp [ne_of_gt hN, ne_of_gt Real.pi_pos]
      ring
    _ ≤ 4 * Real.sin a ^ 2 := by nlinarith
    _ = 4 * Real.sin (Real.pi * (d : Real) / (N : Real)) ^ 2 := by rfl

/-- Every clean Fourier energy is bounded below by the square of its cyclic
label radius, with explicit constant `16/N²`. -/
theorem cycleModeRadius_energy_lower
    (N : Nat) [NeZero N] (j : Site N) :
    16 * (cycleModeRadius N j : Real) ^ 2 / (N : Real) ^ 2 ≤
      cleanCycleModeEnergy N j := by
  have hj : j.val ≤ N := j.val_lt.le
  by_cases h : j.val ≤ N - j.val
  · have h2 : 2 * j.val ≤ N := by omega
    simpa [cycleModeRadius, min_eq_left h, cleanCycleModeEnergy] using
      sineChord_energy_lower (N := N) (d := j.val) h2
  · have hle : N - j.val ≤ j.val := by omega
    have h2 : 2 * (N - j.val) ≤ N := by omega
    have hs := sineChord_energy_lower (N := N) (d := N - j.val) h2
    have hN : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hangle :
        Real.pi * (j.val : Real) / (N : Real) =
          Real.pi - Real.pi * ((N - j.val : Nat) : Real) / (N : Real) := by
      rw [Nat.cast_sub hj]
      field_simp [hN]
      ring
    simp only [cleanCycleModeEnergy]
    rw [hangle, Real.sin_pi_sub]
    simpa [cycleModeRadius, min_eq_right hle] using hs

/-- Elementary upper chord bound `sin² x ≤ x²` for a natural Fourier
representative. -/
theorem cleanCycleModeEnergy_le_valQuadratic
    {N : Nat} [NeZero N] (j : Site N) :
    cleanCycleModeEnergy N j ≤
      4 * Real.pi ^ 2 * (j.val : Real) ^ 2 / (N : Real) ^ 2 := by
  unfold cleanCycleModeEnergy
  calc
    4 * Real.sin (Real.pi * (j.val : Real) / (N : Real)) ^ 2 ≤
        4 * (Real.pi * (j.val : Real) / (N : Real)) ^ 2 := by
      nlinarith [Real.sin_sq_le_sq
        (x := Real.pi * (j.val : Real) / (N : Real))]
    _ = 4 * Real.pi ^ 2 * (j.val : Real) ^ 2 / (N : Real) ^ 2 := by ring


/-- The explicit mode threshold set transported to ordinary representatives
`0, ..., N-1`. -/
def cleanCycleFinModeThresholdIndices
    (N : Nat) [NeZero N] (E : Real) : Finset (Fin N) :=
  Finset.univ.filter fun k ↦
    cleanCycleModeEnergy N (ZMod.finEquiv N k) ≤ E

@[simp] theorem mem_cleanCycleFinModeThresholdIndices_iff
    (N : Nat) [NeZero N] (E : Real) (k : Fin N) :
    k ∈ cleanCycleFinModeThresholdIndices N E ↔
      cleanCycleModeEnergy N (ZMod.finEquiv N k) ≤ E := by
  simp [cleanCycleFinModeThresholdIndices]

/-- `ZMod.finEquiv` preserves the canonical natural representative. -/
theorem finEquiv_val (N : Nat) [NeZero N] (k : Fin N) :
    (ZMod.finEquiv N k).val = k.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- The `ZMod` and `Fin` presentations of the explicit threshold count agree. -/
theorem cleanCycleModeThresholdCount_eq_finCount
    (N : Nat) [NeZero N] (E : Real) :
    cleanCycleModeThresholdCount N E =
      (cleanCycleFinModeThresholdIndices N E).card := by
  unfold cleanCycleModeThresholdCount cleanCycleModeThresholdIndices
  apply Finset.card_equiv (ZMod.finEquiv N).symm.toEquiv
  intro j
  simp [cleanCycleFinModeThresholdIndices]

/-- Explicit lower counting envelope.  If the quadratic upper estimate at
radius `r` is below `E`, then the representatives `0, ..., r` give at least
`r+1` modes below `E`.  This deliberately uses only one side of the cycle. -/
theorem cleanCycleModeThresholdCount_lower_of_quadratic
    (N r : Nat) [NeZero N] (hr : r < N) (E : Real)
    (hE : 4 * Real.pi ^ 2 * (r : Real) ^ 2 / (N : Real) ^ 2 ≤ E) :
    r + 1 ≤ cleanCycleModeThresholdCount N E := by
  rw [cleanCycleModeThresholdCount_eq_finCount]
  let kr : Fin N := ⟨r, hr⟩
  have hsub : Finset.Iic kr ⊆ cleanCycleFinModeThresholdIndices N E := by
    intro k hk
    rw [mem_cleanCycleFinModeThresholdIndices_iff]
    have hkle : k.val ≤ r := by
      exact Fin.le_iff_val_le_val.mp (Finset.mem_Iic.mp hk)
    have hkleR : (k.val : Real) ≤ (r : Real) := by exact_mod_cast hkle
    have hsq : (k.val : Real) ^ 2 ≤ (r : Real) ^ 2 := by
      nlinarith [show 0 ≤ (k.val : Real) by positivity,
        show 0 ≤ (r : Real) by positivity]
    calc
      cleanCycleModeEnergy N (ZMod.finEquiv N k) ≤
          4 * Real.pi ^ 2 *
            ((ZMod.finEquiv N k).val : Real) ^ 2 / (N : Real) ^ 2 :=
        cleanCycleModeEnergy_le_valQuadratic _
      _ = 4 * Real.pi ^ 2 * (k.val : Real) ^ 2 / (N : Real) ^ 2 := by
        rw [finEquiv_val]
      _ ≤ 4 * Real.pi ^ 2 * (r : Real) ^ 2 / (N : Real) ^ 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (by positivity)) (sq_nonneg _)
      _ ≤ E := hE
  calc
    r + 1 = (Finset.Iic kr).card := by simp [kr]
    _ ≤ (cleanCycleFinModeThresholdIndices N E).card :=
      Finset.card_le_card hsub

/-- Ordered-spectrum form of the explicit lower counting envelope. -/
theorem orderedEigenvalueThresholdCount_clean_lower_of_quadratic
    (N r : Nat) [NeZero N] (hr : r < N) (E : Real)
    (hE : 4 * Real.pi ^ 2 * (r : Real) ^ 2 / (N : Real) ^ 2 ≤ E) :
    r + 1 ≤
      orderedEigenvalueThresholdCount (cleanCycleHarmonicHermitian N) E := by
  rw [orderedEigenvalueThresholdCount_clean_eq_modeThresholdCount]
  exact cleanCycleModeThresholdCount_lower_of_quadratic N r hr E hE


/-- Fin representatives whose cyclic radius is at most `r`. -/
def cleanCycleFinRadiusIndices
    (N r : Nat) [NeZero N] : Finset (Fin N) :=
  Finset.univ.filter fun k ↦
    cycleModeRadius N (ZMod.finEquiv N k) ≤ r

@[simp] theorem mem_cleanCycleFinRadiusIndices_iff
    (N r : Nat) [NeZero N] (k : Fin N) :
    k ∈ cleanCycleFinRadiusIndices N r ↔
      cycleModeRadius N (ZMod.finEquiv N k) ≤ r := by
  simp [cleanCycleFinRadiusIndices]

/-- A threshold strictly below the radius-`r+1` chord bound forces every
counted mode to have cyclic radius at most `r`. -/
theorem cleanCycleFinModeThresholdIndices_subset_radius
    (N r : Nat) [NeZero N] (E : Real)
    (hgap : E < 16 * ((r + 1 : Nat) : Real) ^ 2 / (N : Real) ^ 2) :
    cleanCycleFinModeThresholdIndices N E ⊆
      cleanCycleFinRadiusIndices N r := by
  intro k hk
  rw [mem_cleanCycleFinRadiusIndices_iff]
  rw [mem_cleanCycleFinModeThresholdIndices_iff] at hk
  have hlower := cycleModeRadius_energy_lower N (ZMod.finEquiv N k)
  by_contra hrad
  have hnat : r + 1 ≤ cycleModeRadius N (ZMod.finEquiv N k) := by omega
  have hreal : ((r + 1 : Nat) : Real) ≤
      (cycleModeRadius N (ZMod.finEquiv N k) : Real) := by
    exact_mod_cast hnat
  have hsq : ((r + 1 : Nat) : Real) ^ 2 ≤
      (cycleModeRadius N (ZMod.finEquiv N k) : Real) ^ 2 := by
    nlinarith [show 0 ≤ ((r + 1 : Nat) : Real) by positivity,
      show 0 ≤ (cycleModeRadius N (ZMod.finEquiv N k) : Real) by positivity]
  have hscaled :
      16 * ((r + 1 : Nat) : Real) ^ 2 / (N : Real) ^ 2 ≤
        16 * (cycleModeRadius N (ZMod.finEquiv N k) : Real) ^ 2 /
          (N : Real) ^ 2 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (by norm_num)) (sq_nonneg _)
  exact (not_lt_of_ge (hscaled.trans (hlower.trans hk))) hgap

/-- At most `2r+1` labels have cyclic radius at most `r`.  The assumptions
make the two ordinary representative intervals well formed; overlap can only
decrease the union cardinality. -/
theorem cleanCycleFinRadiusIndices_card_le
    (N r : Nat) [NeZero N] (hrpos : 0 < r) (hrN : r < N) :
    (cleanCycleFinRadiusIndices N r).card ≤ 2 * r + 1 := by
  let kr : Fin N := ⟨r, hrN⟩
  have hNr : N - r < N := Nat.sub_lt (NeZero.pos N) hrpos
  let knr : Fin N := ⟨N - r, hNr⟩
  have hsub : cleanCycleFinRadiusIndices N r ⊆
      Finset.Iic kr ∪ Finset.Ici knr := by
    intro k hk
    rw [mem_cleanCycleFinRadiusIndices_iff] at hk
    have hk' : min k.val (N - k.val) ≤ r := by
      simpa [cycleModeRadius, finEquiv_val] using hk
    rw [Finset.mem_union]
    rcases (min_le_iff.mp hk') with hleft | hright
    · left
      rw [Finset.mem_Iic, Fin.le_iff_val_le_val]
      exact hleft
    · right
      rw [Finset.mem_Ici, Fin.le_iff_val_le_val]
      dsimp [knr]
      have hkN : k.val ≤ N := k.isLt.le
      omega
  calc
    (cleanCycleFinRadiusIndices N r).card ≤
        (Finset.Iic kr ∪ Finset.Ici knr).card := Finset.card_le_card hsub
    _ ≤ (Finset.Iic kr).card + (Finset.Ici knr).card :=
      Finset.card_union_le _ _
    _ = 2 * r + 1 := by simp [kr, knr]; omega

/-- Explicit upper counting envelope at a radius-separated threshold. -/
theorem cleanCycleModeThresholdCount_upper_of_chordGap
    (N r : Nat) [NeZero N] (hrpos : 0 < r) (hrN : r < N)
    (E : Real)
    (hgap : E < 16 * ((r + 1 : Nat) : Real) ^ 2 / (N : Real) ^ 2) :
    cleanCycleModeThresholdCount N E ≤ 2 * r + 1 := by
  rw [cleanCycleModeThresholdCount_eq_finCount]
  exact (Finset.card_le_card
    (cleanCycleFinModeThresholdIndices_subset_radius N r E hgap)).trans
      (cleanCycleFinRadiusIndices_card_le N r hrpos hrN)

/-- Ordered-spectrum form of the explicit upper counting envelope. -/
theorem orderedEigenvalueThresholdCount_clean_upper_of_chordGap
    (N r : Nat) [NeZero N] (hrpos : 0 < r) (hrN : r < N)
    (E : Real)
    (hgap : E < 16 * ((r + 1 : Nat) : Real) ^ 2 / (N : Real) ^ 2) :
    orderedEigenvalueThresholdCount (cleanCycleHarmonicHermitian N) E ≤
      2 * r + 1 := by
  rw [orderedEigenvalueThresholdCount_clean_eq_modeThresholdCount]
  exact cleanCycleModeThresholdCount_upper_of_chordGap
    N r hrpos hrN E hgap

/-- Direct ordered-count sandwich combining the quadratic upper chord and
linear lower chord. -/
theorem orderedEigenvalueThresholdCount_clean_sandwich
    (N rLower rUpper : Nat) [NeZero N]
    (hrLower : rLower < N) (hrUpperPos : 0 < rUpper)
    (hrUpper : rUpper < N) (E : Real)
    (hlower : 4 * Real.pi ^ 2 * (rLower : Real) ^ 2 /
      (N : Real) ^ 2 ≤ E)
    (hupper : E < 16 * ((rUpper + 1 : Nat) : Real) ^ 2 /
      (N : Real) ^ 2) :
    rLower + 1 ≤
        orderedEigenvalueThresholdCount (cleanCycleHarmonicHermitian N) E ∧
      orderedEigenvalueThresholdCount (cleanCycleHarmonicHermitian N) E ≤
        2 * rUpper + 1 := by
  exact ⟨orderedEigenvalueThresholdCount_clean_lower_of_quadratic
      N rLower hrLower E hlower,
    orderedEigenvalueThresholdCount_clean_upper_of_chordGap
      N rUpper hrUpperPos hrUpper E hupper⟩


@[simp] theorem cleanCycleModeEnergy_zero (N : Nat) [NeZero N] :
    cleanCycleModeEnergy N (0 : Site N) = 0 := by
  simp [cleanCycleModeEnergy]

/-- The translation label belongs to every nonnegative explicit threshold
set; this is the formal statement that the zero mode is counted. -/
theorem zero_mem_cleanCycleModeThresholdIndices
    (N : Nat) [NeZero N] {E : Real} (hE : 0 ≤ E) :
    (0 : Site N) ∈ cleanCycleModeThresholdIndices N E := by
  rw [mem_cleanCycleModeThresholdIndices_iff]
  simpa using hE

/-- Every nonnegative clean threshold count is at least one, because the
translation zero mode is retained. -/
theorem one_le_orderedEigenvalueThresholdCount_clean_of_nonneg
    (N : Nat) [NeZero N] {E : Real} (hE : 0 ≤ E) :
    1 ≤ orderedEigenvalueThresholdCount (cleanCycleHarmonicHermitian N) E := by
  simpa using orderedEigenvalueThresholdCount_clean_lower_of_quadratic
    N 0 (NeZero.pos N) E (by simpa using hE)

end

end ArchonPhysics.CleanCycleAcousticCountEnvelope
