import ArchonPhysics.ActualTwoMassSpectralJacobianPolynomial
import ArchonPhysics.FreeFPUTDegenerateCorrectionResonanceClassification
import ArchonPhysics.GaussianRandomMassSimpleSpectrum
import ArchonPhysics.ModalPhaseMismatch

/-!
# Gaussian three-site two-to-one resonance nullity

For a three-site periodic random-mass chain there are two positive harmonic
frequencies.  Every dangerous degenerate FPUT mismatch of the form
`omega_parent - 2 * omega_child` therefore lies in the same two-to-one
frequency-ratio event.

This file proves that event null for every verified truncated-Gaussian mass
ensemble.  The proof stays at the frozen finite Hamiltonian level.  It does
not assume independent spectral frequencies or a bounded spectral density:
an exact two-to-one resonance forces the explicit nonzero inverse-mass
polynomial

`16 * (x₀ + x₁ + x₂)^2 - 75 * (x₀*x₁ + x₀*x₂ + x₁*x₂)`

to vanish, and the finite Gaussian mass law avoids that zero set almost
surely.  This is an exact-resonance null theorem, not a quantitative
`P(|Delta| <= delta)` estimate.
-/

namespace ArchonPhysics.GaussianThreeSiteTwoToOneResonanceNull

open ArchonPhysics
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.GaussianRandomMassSimpleSpectrum
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDegenerateCorrectionResonanceClassification
open ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.TruncatedGaussianMassLaw
open MeasureTheory

noncomputable section

/-! ## The explicit three-site characteristic polynomial -/

/-- The general three-cycle weighted Laplacian in canonical `Fin 3`
coordinates. -/
def explicitThreeCycleLaplacianCoordinates (x : Fin 3 → Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  !![x 0 + x 1, -x 1, -x 0;
     -x 1, x 1 + x 2, -x 2;
     -x 0, -x 2, x 0 + x 2]

/-- Reindexing the genuine weighted cycle to `Fin 3` gives the displayed
three-coordinate matrix. -/
theorem finWeightedCycleLaplacian_threeSite_coordinates
    (x : Fin 3 → Real) :
    finWeightedCycleLaplacian x =
      explicitThreeCycleLaplacianCoordinates x := by
  rw [finWeightedCycleLaplacian_eq_sum_rankOne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Fin.sum_univ_succ]
  <;> norm_num +decide [explicitThreeCycleLaplacianCoordinates,
    finCycleEdgeVector,
    SingleMassRankOnePerturbation.cycleMassPerturbationVector,
    differenceMatrix, siteEquivFin]

/-- The zero translation root and the two positive roots are exposed by the
general three-cycle characteristic polynomial. -/
theorem explicitThreeCycleLaplacianCoordinates_charpoly_eval
    (x : Fin 3 → Real) (energy : Real) :
    (explicitThreeCycleLaplacianCoordinates x).charpoly.eval energy =
      energy * (energy ^ 2 -
        2 * (x 0 + x 1 + x 2) * energy +
        3 * (x 0 * x 1 + x 0 * x 2 + x 1 * x 2)) := by
  rw [Matrix.eval_charpoly, Matrix.det_fin_three]
  simp [explicitThreeCycleLaplacianCoordinates, Matrix.scalar_apply]
  ring

/-- Characteristic-polynomial formula for the genuine mass-weighted
three-site Hamiltonian in its three inverse-mass coordinates. -/
theorem threeSite_massWeightedHarmonic_charpoly_eval
    (m : Lattice.PositiveMassConfig 3) (energy : Real) :
    (massWeightedHarmonicMatrix m).charpoly.eval energy =
      energy * (energy ^ 2 -
        2 * (inverseMassCoordinates m 0 + inverseMassCoordinates m 1 +
          inverseMassCoordinates m 2) * energy +
        3 * (inverseMassCoordinates m 0 * inverseMassCoordinates m 1 +
          inverseMassCoordinates m 0 * inverseMassCoordinates m 2 +
          inverseMassCoordinates m 1 * inverseMassCoordinates m 2)) := by
  have hchar :
      (massWeightedHarmonicMatrix m).charpoly =
        (finWeightedCycleLaplacian (inverseMassCoordinates m)).charpoly := by
    calc
      (massWeightedHarmonicMatrix m).charpoly =
          (massWeightedDifferenceMatrix m *
            Matrix.transpose (massWeightedDifferenceMatrix m)).charpoly :=
        Matrix.charpoly_mul_comm
          (Matrix.transpose (massWeightedDifferenceMatrix m))
          (massWeightedDifferenceMatrix m)
      _ = (weightedCycleLaplacian (fun i => (m.mass i)⁻¹)).charpoly := by
        rw [massWeighted_selfTranspose_eq_weightedCycleLaplacian]
      _ = (weightedCycleLaplacian
          (weightsOfCoordinates (inverseMassCoordinates m))).charpoly := by
        rw [weightsOfCoordinates_inverseMassCoordinates]
      _ = (finWeightedCycleLaplacian
          (inverseMassCoordinates m)).charpoly := by
        symm
        exact Matrix.charpoly_reindex _ _
  rw [hchar, finWeightedCycleLaplacian_threeSite_coordinates,
    explicitThreeCycleLaplacianCoordinates_charpoly_eval]

/-! ## Polynomial obstruction for a two-to-one modal ratio -/

/-- The nonzero inverse-mass polynomial forced to vanish by any positive
two-to-one frequency ratio in the three-site chain. -/
def threeSiteTwoToOneResonancePolynomial : MvPolynomial (Fin 3) Real :=
  let total := MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2
  let pairSum :=
    MvPolynomial.X 0 * MvPolynomial.X 1 +
      MvPolynomial.X 0 * MvPolynomial.X 2 +
      MvPolynomial.X 1 * MvPolynomial.X 2
  16 * total ^ 2 - 75 * pairSum

@[simp] theorem eval_threeSiteTwoToOneResonancePolynomial
    (x : Fin 3 → Real) :
    MvPolynomial.eval x threeSiteTwoToOneResonancePolynomial =
      16 * (x 0 + x 1 + x 2) ^ 2 -
        75 * (x 0 * x 1 + x 0 * x 2 + x 1 * x 2) := by
  simp [threeSiteTwoToOneResonancePolynomial]

theorem threeSiteTwoToOneResonancePolynomial_ne_zero :
    threeSiteTwoToOneResonancePolynomial ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (![1, 1, 1] : Fin 3 → Real)) hzero
  rw [eval_threeSiteTwoToOneResonancePolynomial] at heval
  simp only [map_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at heval
  norm_num at heval

/-- Every raw Hermitian eigenvalue used by `modeFrequencySq` is a root of the
physical characteristic polynomial. -/
theorem massWeightedHarmonic_charpoly_eval_modeFrequencySq_eq_zero
    (m : Lattice.PositiveMassConfig 3) (mode : Lattice.Site 3) :
    (massWeightedHarmonicMatrix m).charpoly.eval
        (modeFrequencySq m mode) = 0 := by
  let h : (massWeightedHarmonicMatrix m).IsHermitian := by
    unfold massWeightedHarmonicMatrix Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul]
    simp
  rw [h.charpoly_eq]
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ mode)
  simp [modeFrequencySq]

/-- A positive modal squared frequency obeys the positive quadratic factor
of the three-site characteristic polynomial. -/
theorem threeSite_modeFrequencySq_quadratic_eq_zero
    (m : Lattice.PositiveMassConfig 3) (mode : Lattice.Site 3)
    (hpositive : 0 < modeFrequency m mode) :
    modeFrequencySq m mode ^ 2 -
        2 * (inverseMassCoordinates m 0 + inverseMassCoordinates m 1 +
          inverseMassCoordinates m 2) * modeFrequencySq m mode +
        3 * (inverseMassCoordinates m 0 * inverseMassCoordinates m 1 +
          inverseMassCoordinates m 0 * inverseMassCoordinates m 2 +
          inverseMassCoordinates m 1 * inverseMassCoordinates m 2) = 0 := by
  have hroot :=
    massWeightedHarmonic_charpoly_eval_modeFrequencySq_eq_zero m mode
  rw [threeSite_massWeightedHarmonic_charpoly_eval] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left (by
    rw [← modeFrequency_sq]
    positivity)

/-- Deterministic Hamiltonian reduction: any positive two-to-one modal
frequency ratio forces the explicit inverse-mass polynomial to vanish. -/
theorem eval_threeSiteTwoToOneResonancePolynomial_eq_zero_of_frequency_ratio
    (m : Lattice.PositiveMassConfig 3)
    (parent child : Lattice.Site 3)
    (hchild : 0 < modeFrequency m child)
    (hratio : modeFrequency m parent = 2 * modeFrequency m child) :
    MvPolynomial.eval (inverseMassCoordinates m)
      threeSiteTwoToOneResonancePolynomial = 0 := by
  let total := inverseMassCoordinates m 0 + inverseMassCoordinates m 1 +
    inverseMassCoordinates m 2
  let pairSum :=
    inverseMassCoordinates m 0 * inverseMassCoordinates m 1 +
      inverseMassCoordinates m 0 * inverseMassCoordinates m 2 +
      inverseMassCoordinates m 1 * inverseMassCoordinates m 2
  let childSq := modeFrequencySq m child
  have hparent : 0 < modeFrequency m parent := by
    rw [hratio]
    positivity
  have hparentEquation :=
    threeSite_modeFrequencySq_quadratic_eq_zero m parent hparent
  have hchildEquation :=
    threeSite_modeFrequencySq_quadratic_eq_zero m child hchild
  have hsq : modeFrequencySq m parent = 4 * childSq := by
    dsimp only [childSq]
    rw [← modeFrequency_sq, ← modeFrequency_sq, hratio]
    ring
  change modeFrequencySq m parent ^ 2 -
      2 * total * modeFrequencySq m parent + 3 * pairSum = 0 at hparentEquation
  change childSq ^ 2 - 2 * total * childSq + 3 * pairSum = 0 at hchildEquation
  rw [hsq] at hparentEquation
  have hchildSqPos : 0 < childSq := by
    dsimp only [childSq]
    rw [← modeFrequency_sq]
    positivity
  have hfactor : 3 * childSq * (5 * childSq - 2 * total) = 0 := by
    nlinarith [hparentEquation, hchildEquation]
  have hlinear : 5 * childSq - 2 * total = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero (by norm_num)
      (ne_of_gt hchildSqPos))
  rw [eval_threeSiteTwoToOneResonancePolynomial]
  change 16 * total ^ 2 - 75 * pairSum = 0
  nlinarith [hchildEquation, hlinear]

/-! ## Direct bridges from the three classified dangerous sectors -/

/-- Exact resonance in the repeated-away dangerous sector forces the
three-site inverse-mass obstruction polynomial to vanish. -/
theorem eval_resonancePolynomial_eq_zero_of_repeatedAway_resonant
    (m : Lattice.PositiveMassConfig 3) (observed : Lattice.Site 3)
    (q : QuadraticPhaseTerm 3)
    (hq : q ∈ repeatedAwayPotentiallyResonantSameSignRepresentatives
      3 m observed)
    (hresonant : IsResonant m (quadraticCollisionSign q)
      (quadraticCollisionModes observed q)) :
    MvPolynomial.eval (inverseMassCoordinates m)
      threeSiteTwoToOneResonancePolynomial = 0 := by
  classical
  have hbase := (Finset.mem_filter.mp hq).1
  have hqMem :=
    ((mem_positiveRepeatedChildSameSignRepresentatives_iff
      m observed q).1 hbase).1
  have hPositive : PositiveModeTuple m
      (quadraticCollisionModes observed q) := by
    simpa [positiveQuadraticSwapOrbitRepresentatives] using
      (Finset.mem_filter.mp hqMem).2
  have hchild : 0 < modeFrequency m (q.1 0) := by
    simpa [quadraticCollisionModes] using hPositive (Fin.succ 0)
  exact eval_threeSiteTwoToOneResonancePolynomial_eq_zero_of_frequency_ratio
    m observed (q.1 0) hchild
      ((isResonant_repeatedAwayPotentiallyResonant_iff
        m observed q hq).1 hresonant)

set_option maxRecDepth 2000 in
/-- Exact resonance in the carrier-observed dangerous sector forces the same
two-to-one inverse-mass obstruction. -/
theorem eval_resonancePolynomial_eq_zero_of_observedCarrier_resonant
    (m : Lattice.PositiveMassConfig 3) (observed : Lattice.Site 3)
    (parameter : PositiveObservedCarrierParameter 3 m observed)
    (hParameter : parameter ∈
      observedCarrierPotentiallyResonantParameters m observed)
    (hresonant : IsResonant m (quadraticCollisionSign parameter.q)
      (quadraticCollisionModes observed parameter.q)) :
    MvPolynomial.eval (inverseMassCoordinates m)
      threeSiteTwoToOneResonancePolynomial = 0 := by
  classical
  have hPositive : PositiveModeTuple m
      (quadraticCollisionModes observed parameter.q) := by
    simpa [positiveQuadraticSwapOrbitRepresentatives] using
      (Finset.mem_filter.mp parameter.q_mem).2
  have hObserved : 0 < modeFrequency m observed := by
    simpa [quadraticCollisionModes] using hPositive 0
  have hratio : modeFrequency m
        (parameter.q.1 (otherQuadraticSlot parameter.selected)) =
      2 * modeFrequency m observed :=
    (isResonant_observedCarrierPotentiallyResonant_iff
      m observed parameter hParameter).1 hresonant
  exact eval_threeSiteTwoToOneResonancePolynomial_eq_zero_of_frequency_ratio
    m (parameter.q.1 (otherQuadraticSlot parameter.selected)) observed
      hObserved hratio

set_option maxRecDepth 2000 in
/-- Exact resonance in the free-observed dangerous sector forces the same
two-to-one inverse-mass obstruction. -/
theorem eval_resonancePolynomial_eq_zero_of_observedFree_resonant
    (m : Lattice.PositiveMassConfig 3) (observed : Lattice.Site 3)
    (parameter : PositiveObservedFreeConnectedParameter 3 m observed)
    (hParameter : parameter ∈
      observedFreePotentiallyResonantParameters m observed)
    (hresonant : IsResonant m (quadraticCollisionSign parameter.q)
      (quadraticCollisionModes observed parameter.q)) :
    MvPolynomial.eval (inverseMassCoordinates m)
      threeSiteTwoToOneResonancePolynomial = 0 := by
  classical
  have hPositive : PositiveModeTuple m
      (quadraticCollisionModes observed parameter.q) := by
    simpa [positiveQuadraticSwapOrbitRepresentatives] using
      (Finset.mem_filter.mp parameter.q_mem).2
  have hObserved : 0 < modeFrequency m observed := by
    simpa [quadraticCollisionModes] using hPositive 0
  have hratio : modeFrequency m (parameter.q.1 parameter.selected) =
      2 * modeFrequency m observed :=
    (isResonant_observedFreePotentiallyResonant_iff
      m observed parameter hParameter).1 hresonant
  exact eval_threeSiteTwoToOneResonancePolynomial_eq_zero_of_frequency_ratio
    m (parameter.q.1 parameter.selected) observed hObserved hratio

/-! ## Gaussian annealed resonance-null endpoints -/

/-- At three sites, the probability that any two modal labels have a positive
two-to-one frequency ratio is zero under the genuine truncated-Gaussian mass
law. -/
theorem probability_exists_positive_twoToOne_modeFrequency_eq_zero
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega) :
    ensemble.probability
        {omega | ∃ parent child : Lattice.Site 3,
          0 < modeFrequency
              (ensemble.restrictPositiveMass (N := 3) omega) child ∧
            modeFrequency
                (ensemble.restrictPositiveMass (N := 3) omega) parent =
              2 * modeFrequency
                (ensemble.restrictPositiveMass (N := 3) omega) child} = 0 := by
  apply measure_mono_null (t :=
    {omega | MvPolynomial.eval
      (coordinatewiseInv (restrictMassFin ensemble (N := 3) omega))
      threeSiteTwoToOneResonancePolynomial = 0})
  · rintro omega ⟨parent, child, hchild, hratio⟩
    have hvanish :=
      eval_threeSiteTwoToOneResonancePolynomial_eq_zero_of_frequency_ratio
        (ensemble.restrictPositiveMass (N := 3) omega)
          parent child hchild hratio
    rwa [inverseMassCoordinates_restrictPositiveMass] at hvanish
  · exact probability_eval_inverse_restrictMassFin_eq_zero ensemble
      threeSiteTwoToOneResonancePolynomial
      threeSiteTwoToOneResonancePolynomial_ne_zero

/-- Equivalent mismatch-zero form, matching all three dangerous degenerate
FPUT scalar denominators after assigning their doubled leg as `child`. -/
theorem probability_exists_positive_twoToOne_mismatch_eq_zero
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega) :
    ensemble.probability
        {omega | ∃ parent child : Lattice.Site 3,
          0 < modeFrequency
              (ensemble.restrictPositiveMass (N := 3) omega) child ∧
            modeFrequency
                (ensemble.restrictPositiveMass (N := 3) omega) parent -
              2 * modeFrequency
                (ensemble.restrictPositiveMass (N := 3) omega) child = 0} = 0 := by
  apply measure_mono_null (t :=
    {omega | ∃ parent child : Lattice.Site 3,
      0 < modeFrequency
          (ensemble.restrictPositiveMass (N := 3) omega) child ∧
        modeFrequency
            (ensemble.restrictPositiveMass (N := 3) omega) parent =
          2 * modeFrequency
            (ensemble.restrictPositiveMass (N := 3) omega) child})
  · rintro omega ⟨parent, child, hchild, hmismatch⟩
    exact ⟨parent, child, hchild, by linarith⟩
  · exact probability_exists_positive_twoToOne_modeFrequency_eq_zero ensemble

/-- Fixed-mode form suitable for one resolved dangerous correction summand. -/
theorem probability_fixed_positive_twoToOne_mismatch_eq_zero
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    (parent child : Lattice.Site 3) :
    ensemble.probability
        {omega |
          0 < modeFrequency
              (ensemble.restrictPositiveMass (N := 3) omega) child ∧
            modeFrequency
                (ensemble.restrictPositiveMass (N := 3) omega) parent -
              2 * modeFrequency
                (ensemble.restrictPositiveMass (N := 3) omega) child = 0} = 0 := by
  apply measure_mono_null (t :=
    {omega | ∃ parent child : Lattice.Site 3,
      0 < modeFrequency
          (ensemble.restrictPositiveMass (N := 3) omega) child ∧
        modeFrequency
            (ensemble.restrictPositiveMass (N := 3) omega) parent -
          2 * modeFrequency
            (ensemble.restrictPositiveMass (N := 3) omega) child = 0})
  · intro omega hzero
    exact ⟨parent, child, hzero⟩
  · exact probability_exists_positive_twoToOne_mismatch_eq_zero ensemble

/-- Almost-everywhere nonresonance interface for one fixed positive doubled
leg.  Positivity is kept as an implication because the raw Hermitian modal
labelling includes the unique translation zero mode. -/
theorem fixed_positive_twoToOne_mismatch_ne_zero_ae
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    (parent child : Lattice.Site 3) :
    ∀ᵐ omega ∂ensemble.probability,
      0 < modeFrequency
          (ensemble.restrictPositiveMass (N := 3) omega) child →
        modeFrequency
            (ensemble.restrictPositiveMass (N := 3) omega) parent -
          2 * modeFrequency
            (ensemble.restrictPositiveMass (N := 3) omega) child ≠ 0 := by
  have hnull := probability_fixed_positive_twoToOne_mismatch_eq_zero
    ensemble parent child
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with omega hnot
  intro hpositive hzero
  exact hnot ⟨hpositive, hzero⟩

end

end ArchonPhysics.GaussianThreeSiteTwoToOneResonanceNull
