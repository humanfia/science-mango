import ArchonPhysics.PathLaplacianResultant
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet

/-!
# Nonvanishing of the actual two-mass repeated-root slice

The spectrum polynomial exposed by the algebraic A2 bad-set audit is never
the zero polynomial when the two varied sites are distinct.  The proof is a
finite-dimensional specialization argument valid for every positive frozen
background.

Set the inverse mass at the first varied site to zero and retain the frozen
positive inverse mass at every other site.  This cuts the weighted cycle at
one edge and leaves a weighted path with every remaining edge strictly
positive.  A direct recurrence proves that an eigenvector of this path is
determined by its value at the cut vertex.  Hence every eigenspace has
dimension at most one; Hermitian diagonalization then gives a separable full
characteristic polynomial, including a simple acoustic zero root.  Its
characteristic resultant is nonzero, so evaluation at the cut specialization
proves the two-variable slice polynomial nonzero.

The file also records a physically supported reduction: one supported
two-mass point with simple full ordered spectrum is already enough to prove
slice nonvanishing.  This auxiliary route keeps the acoustic zero mode inside
the full separability statement rather than confusing positive-spectrum
simplicity with simplicity of the zero root.
-/

namespace ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PathLaplacianResultant
open ArchonPhysics.PathLaplacianSpecialization
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance

noncomputable section

/-- Two distinct periodic sites force the volume to contain at least two
sites. -/
theorem volume_ge_two_of_sites_ne
    {N : Nat} [NeZero N] {site₁ site₂ : Lattice.Site N}
    (hsite : site₁ ≠ site₂) : 2 ≤ N := by
  have hcard : 1 < Fintype.card (Lattice.Site N) :=
    Fintype.one_lt_card_iff.mpr ⟨site₁, site₂, hsite⟩
  rw [ZMod.card] at hcard
  omega

/-! ## Arbitrary positive weighted paths have simple full spectrum -/

/-- An eigenvector of a weighted cycle cut at one edge is determined by its
coordinate at the cut vertex, provided every remaining edge weight is
strictly positive. -/
theorem weightedPath_eigenvector_zero_of_zero_cut
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (w : Lattice.Configuration N) (cut : Lattice.Site N)
    (hcut : w cut = 0)
    (hpositive : ∀ i, i ≠ cut → 0 < w i)
    (q : Lattice.Configuration N) (lambda : Real)
    (heigen : Matrix.mulVec (weightedCycleLaplacian w) q = lambda • q)
    (hqCut : q cut = 0) : q = 0 := by
  have hone : cut + 1 ≠ cut := by
    intro h
    have honeZero : (1 : Lattice.Site N) = 0 := by
      simpa using congrArg (fun z : Lattice.Site N ↦ z - cut) h
    rw [ZMod.one_eq_zero_iff] at honeZero
    omega
  have hqOne : q (cut + 1) = 0 := by
    have hrow := congrFun heigen cut
    rw [weightedCycleLaplacian_mulVec] at hrow
    change
      w (cut + 1) * (q cut - q (cut + 1)) +
          w cut * (q cut - q (cut - 1)) = lambda * q cut at hrow
    rw [hcut, hqCut] at hrow
    simp only [zero_sub, zero_mul, mul_zero] at hrow
    have hweight : w (cut + 1) ≠ 0 := ne_of_gt (hpositive _ hone)
    have hproduct : w (cut + 1) * q (cut + 1) = 0 := by
      nlinarith [hrow]
    exact (mul_eq_zero.mp hproduct).resolve_left hweight
  have hall : ∀ k : Nat, k < N → q (cut + (k : Lattice.Site N)) = 0 := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero =>
        intro _
        simpa using hqCut
    | one =>
        intro _
        simpa using hqOne
    | more k hk hkOne =>
        intro hkTwoN
        have hkN : k < N := by omega
        have hkOneN : k + 1 < N := by omega
        have hcurrentNe : cut + ((k + 1 : Nat) : Lattice.Site N) ≠ cut := by
          intro h
          have hzero : ((k + 1 : Nat) : Lattice.Site N) = 0 := by
            simpa using congrArg (fun z : Lattice.Site N ↦ z - cut) h
          rw [ZMod.natCast_eq_zero_iff] at hzero
          exact (Nat.not_dvd_of_pos_of_lt (by omega) hkOneN) hzero
        have hnextNe : cut + ((k + 2 : Nat) : Lattice.Site N) ≠ cut := by
          intro h
          have hzero : ((k + 2 : Nat) : Lattice.Site N) = 0 := by
            simpa using congrArg (fun z : Lattice.Site N ↦ z - cut) h
          rw [ZMod.natCast_eq_zero_iff] at hzero
          exact (Nat.not_dvd_of_pos_of_lt (by omega) hkTwoN) hzero
        have hprev :
            (cut + ((k + 1 : Nat) : Lattice.Site N)) - 1 =
              cut + (k : Lattice.Site N) := by
          push_cast
          ring
        have hnext :
            (cut + ((k + 1 : Nat) : Lattice.Site N)) + 1 =
              cut + ((k + 2 : Nat) : Lattice.Site N) := by
          push_cast
          ring
        have hrow := congrFun heigen
          (cut + ((k + 1 : Nat) : Lattice.Site N))
        rw [weightedCycleLaplacian_mulVec] at hrow
        change
          w ((cut + ((k + 1 : Nat) : Lattice.Site N)) + 1) *
                (q (cut + ((k + 1 : Nat) : Lattice.Site N)) -
                  q ((cut + ((k + 1 : Nat) : Lattice.Site N)) + 1)) +
              w (cut + ((k + 1 : Nat) : Lattice.Site N)) *
                (q (cut + ((k + 1 : Nat) : Lattice.Site N)) -
                  q ((cut + ((k + 1 : Nat) : Lattice.Site N)) - 1)) =
            lambda * q (cut + ((k + 1 : Nat) : Lattice.Site N)) at hrow
        rw [hprev, hnext, hk hkN, hkOne hkOneN] at hrow
        simp only [zero_sub, sub_self, mul_zero, add_zero] at hrow
        have hweight :
            w (cut + ((k + 2 : Nat) : Lattice.Site N)) ≠ 0 :=
          ne_of_gt (hpositive _ hnextNe)
        have hproduct :
            w (cut + ((k + 2 : Nat) : Lattice.Site N)) *
              q (cut + ((k + 2 : Nat) : Lattice.Site N)) = 0 := by
          nlinarith [hrow]
        exact (mul_eq_zero.mp hproduct).resolve_left hweight
  ext i
  let displacement : Lattice.Site N := i - cut
  have hzero := hall displacement.val displacement.val_lt
  have hcast : ((displacement.val : Nat) : Lattice.Site N) = displacement :=
    ZMod.natCast_zmod_val displacement
  rw [hcast] at hzero
  simpa [displacement] using hzero

/-- A one-cut cycle with all remaining weights positive has no
two-dimensional eigenspace at any real eigenvalue. -/
theorem not_hasGeometricMultiplicityTwo_weightedPath
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (w : Lattice.Configuration N) (cut : Lattice.Site N)
    (hcut : w cut = 0)
    (hpositive : ∀ i, i ≠ cut → 0 < w i) :
    ¬ HasGeometricMultiplicityTwo (weightedCycleLaplacian w) := by
  rintro ⟨lambda, v, hv, heigen⟩
  have hv_ne (j : Fin 2) : v j ≠ 0 := hv.ne_zero j
  have hcut_ne (j : Fin 2) : v j cut ≠ 0 := by
    intro hzero
    apply hv_ne j
    exact weightedPath_eigenvector_zero_of_zero_cut hN w cut hcut
      hpositive (v j) lambda (heigen j) hzero
  let q : Lattice.Configuration N :=
    v 1 cut • v 0 - v 0 cut • v 1
  have hqEigen :
      Matrix.mulVec (weightedCycleLaplacian w) q = lambda • q := by
    unfold q
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      heigen 0, heigen 1]
    simp [smul_sub, smul_smul, mul_comm]
  have hqCut : q cut = 0 := by
    simp [q]
    ring
  have hq : q = 0 :=
    weightedPath_eigenvector_zero_of_zero_cut hN w cut hcut hpositive
      q lambda hqEigen hqCut
  have hsum :
      (∑ j : Fin 2, ![v 1 cut, -v 0 cut] j • v j) = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa [q, sub_eq_add_neg, neg_smul] using hq
  have hcoeff := (Fintype.linearIndependent_iff.mp hv)
    ![v 1 cut, -v 0 cut] hsum (0 : Fin 2)
  exact hcut_ne 1 (by simpa using hcoeff)

/-- The Hermitian eigenvalue enumeration is injective for every positive
weighted path, including its acoustic zero eigenvalue. -/
theorem weightedPath_eigenvalues_injective
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (w : Lattice.Configuration N) (cut : Lattice.Site N)
    (hcut : w cut = 0)
    (hpositive : ∀ i, i ≠ cut → 0 < w i) :
    Function.Injective
      (weightedCycleLaplacian_isHermitian w).eigenvalues := by
  let hA := weightedCycleLaplacian_isHermitian w
  intro i j hij
  by_contra hne
  apply not_hasGeometricMultiplicityTwo_weightedPath hN w cut hcut hpositive
  let f : Fin 2 → Lattice.Site N := ![i, j]
  have hf : Function.Injective f := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [f, hne, Ne.symm hne]
  let v : Fin 2 → Lattice.Configuration N :=
    fun k ↦ ⇑(hA.eigenvectorBasis (f k))
  have hv : LinearIndependent Real v := by
    have hb := hA.eigenvectorBasis.toBasis.linearIndependent.comp f hf
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    ext x
    have hx := congrFun hg x
    simpa [v, Function.comp_def] using hx
  refine ⟨hA.eigenvalues i, v, hv, ?_⟩
  intro k
  fin_cases k
  · simpa [v, f, hA] using hA.mulVec_eigenvectorBasis i
  · simpa [v, f, hA, hij] using hA.mulVec_eigenvectorBasis j

/-- Full characteristic separability for an arbitrary positive weighted
path. -/
theorem weightedPath_charpoly_separable
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (w : Lattice.Configuration N) (cut : Lattice.Site N)
    (hcut : w cut = 0)
    (hpositive : ∀ i, i ≠ cut → 0 < w i) :
    (weightedCycleLaplacian w).charpoly.Separable := by
  let hA := weightedCycleLaplacian_isHermitian w
  rw [hA.charpoly_eq]
  exact Polynomial.separable_prod_X_sub_C_iff.mpr
    (weightedPath_eigenvalues_injective hN w cut hcut hpositive)

/-- The fixed-size characteristic resultant is nonzero at every positive
weighted-path specialization. -/
theorem weightedPath_fixedResultant_ne_zero
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (w : Lattice.Configuration N) (cut : Lattice.Site N)
    (hcut : w cut = 0)
    (hpositive : ∀ i, i ≠ cut → 0 < w i) :
    let A := weightedCycleLaplacian w
    Polynomial.resultant A.charpoly A.charpoly.derivative
      (Fintype.card (Lattice.Site N))
      (Fintype.card (Lattice.Site N) - 1) ≠ 0 := by
  dsimp only
  let A := weightedCycleLaplacian w
  have hsep : A.charpoly.Separable :=
    weightedPath_charpoly_separable hN w cut hcut hpositive
  have hunit : IsUnit (Polynomial.resultant A.charpoly A.charpoly.derivative) :=
    (Polynomial.isUnit_resultant_iff_isCoprime
      (Matrix.charpoly_monic A)).mpr hsep
  have hne : Polynomial.resultant A.charpoly A.charpoly.derivative ≠ 0 :=
    IsUnit.ne_zero hunit
  simpa [Matrix.charpoly_natDegree_eq_dim,
    Polynomial.natDegree_derivative] using hne

/-! ## The actual arbitrary-background two-site slice -/

/-- Algebraic inverse-mass weights obtained by cutting the first varied site
and retaining every other frozen inverse mass. -/
def cutFirstInverseMassWeights
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ : Lattice.Site N) : Lattice.Configuration N :=
  fun site ↦ if site = site₁ then 0 else (fixed.mass site)⁻¹

@[simp] theorem cutFirstInverseMassWeights_at_cut
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ : Lattice.Site N) :
    cutFirstInverseMassWeights fixed site₁ site₁ = 0 := by
  simp [cutFirstInverseMassWeights]

theorem cutFirstInverseMassWeights_pos_of_ne
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site : Lattice.Site N} (hne : site ≠ site₁) :
    0 < cutFirstInverseMassWeights fixed site₁ site := by
  simp [cutFirstInverseMassWeights, hne, inv_pos.mpr (fixed.mass_pos site)]

/-- The inverse-coordinate slice evaluated at raw pair `(0, fixed mass at
the second site)` is exactly the one-cut positive weighted path. -/
theorem twoSiteInverseMassSliceCoordinates_cut_pair
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂) :
    weightsOfCoordinates
        (twoSiteInverseMassSliceCoordinates fixed site₁ site₂
          (0, fixed.mass site₂)) =
      cutFirstInverseMassWeights fixed site₁ := by
  ext site
  simp only [weightsOfCoordinates, twoSiteInverseMassSliceCoordinates,
    cutFirstInverseMassWeights]
  let k := siteEquivFin N site
  have hround : (siteEquivFin N).symm k = site := by
    exact (siteEquivFin N).symm_apply_apply site
  rw [show site = (siteEquivFin N).symm k by exact hround.symm]
  by_cases hfirst : (siteEquivFin N).symm k = site₁
  · simp [hfirst]
  by_cases hsecond : (siteEquivFin N).symm k = site₂
  · simp [hsecond, hsite.symm]
  · simp [hfirst, hsecond]

/-- Main spectrum certificate: for every positive frozen background and any
two distinct varied sites, the concrete two-variable repeated-root resultant
restriction is genuinely nonzero. -/
theorem twoSiteRepeatedRootSlicePolynomial_ne_zero
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂) :
    twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂ ≠ 0 := by
  intro hzero
  let pair : Real × Real := (0, fixed.mass site₂)
  have heval := congrArg
    (MvPolynomial.eval (iidInverseMassPairCoordinates pair)) hzero
  rw [evaluate_twoSiteRepeatedRootSlicePolynomial,
    evaluate_symbolicRepeatedRootCertificate] at heval
  simp only [map_zero] at heval
  have hweights := twoSiteInverseMassSliceCoordinates_cut_pair fixed hsite
  have hN : 2 ≤ N := volume_ge_two_of_sites_ne hsite
  have hresultant := weightedPath_fixedResultant_ne_zero hN
    (cutFirstInverseMassWeights fixed site₁) site₁
    (cutFirstInverseMassWeights_at_cut fixed site₁)
    (fun i hi ↦ cutFirstInverseMassWeights_pos_of_ne fixed hi)
  rw [hweights] at heval
  exact hresultant heval

/-- Construct the complete algebraic regularity certificate from only the
channel-specific Jacobian eliminant.  The spectrum-polynomial obligation is
discharged unconditionally by the positive weighted-path specialization. -/
def algebraicRegularityCertificateOfJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N}
    (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hsite : site₁ ≠ site₂)
    (jacobianPolynomial : MvPolynomial (Fin 2) Real)
    (hjacobian : jacobianPolynomial ≠ 0)
    (helimination :
      ∀ pair ∈ interior iidMassPairSupport,
        SimpleOrderedSpectrum
            (twoSiteHarmonicHermitian fixed site₁ site₂ pair) →
        physlibIteratedA2PairMismatchVerticalJacobian
            fixed site₁ site₂ channel observed term pair = 0 →
        MvPolynomial.eval (iidInverseMassPairCoordinates pair)
            jacobianPolynomial = 0) :
    IteratedA2PairAlgebraicRegularityCertificate
      fixed site₁ site₂ channel observed term where
  site_ne := hsite
  spectrumPolynomial_ne_zero :=
    twoSiteRepeatedRootSlicePolynomial_ne_zero fixed hsite
  jacobianPolynomial := jacobianPolynomial
  jacobianPolynomial_ne_zero := hjacobian
  jacobian_zero_forces_polynomial_zero := helimination

/-! ## A supported simple-spectrum witness also suffices -/

/-- Injectivity of the decreasing ordered Hermitian spectrum implies full
characteristic separability. -/
theorem charpoly_separable_of_simpleOrderedSpectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A) :
    (Matrix.charpoly A.1).Separable := by
  rw [A.2.charpoly_eq]
  apply Polynomial.separable_prod_X_sub_C_iff.mpr
  intro i j hij
  apply (orderedIndexEquiv : Fin (Fintype.card ι) ≃ ι).symm.injective
  apply hsimple
  rw [← orderedEigenvalue_equiv A, ← orderedEigenvalue_equiv A]
  simpa using hij

/-- A supported actual two-site point with simple full ordered spectrum gives
a nonzero evaluation of the restricted repeated-root resultant. -/
theorem twoSiteRepeatedRootSlicePolynomial_eval_ne_zero_of_simple
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair)) :
    MvPolynomial.eval (iidInverseMassPairCoordinates pair)
      (twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂) ≠ 0 := by
  let m := twoSiteMassConfig fixed site₁ site₂ pair
  let H : Matrix (Lattice.Site N) (Lattice.Site N) Real :=
    massWeightedHarmonicMatrix m
  let W : Matrix (Lattice.Site N) (Lattice.Site N) Real :=
    weightedCycleLaplacian (fun i ↦ (m.mass i)⁻¹)
  have hchar : W.charpoly = H.charpoly := by
    calc
      W.charpoly =
          (massWeightedDifferenceMatrix m *
            Matrix.transpose (massWeightedDifferenceMatrix m)).charpoly := by
        rw [massWeighted_selfTranspose_eq_weightedCycleLaplacian]
      _ = H.charpoly := by
        exact Matrix.charpoly_mul_comm
          (massWeightedDifferenceMatrix m)
          (Matrix.transpose (massWeightedDifferenceMatrix m))
  have hsepH : H.charpoly.Separable := by
    simpa [H, m, twoSiteHarmonicHermitian, harmonicHermitian] using
      charpoly_separable_of_simpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair) hsimple
  have hsepW : W.charpoly.Separable := by simpa [hchar] using hsepH
  have hunit : IsUnit
      (Polynomial.resultant W.charpoly W.charpoly.derivative) :=
    (Polynomial.isUnit_resultant_iff_isCoprime
      (Matrix.charpoly_monic W)).mpr hsepW
  have hresultant :
      Polynomial.resultant W.charpoly W.charpoly.derivative
        (Fintype.card (Lattice.Site N))
        (Fintype.card (Lattice.Site N) - 1) ≠ 0 := by
    simpa [Matrix.charpoly_natDegree_eq_dim,
      Polynomial.natDegree_derivative] using (IsUnit.ne_zero hunit)
  rw [evaluate_twoSiteRepeatedRootSlicePolynomial,
    ← inverseMassCoordinates_twoSiteMassConfig_of_mem_support
      fixed hsite hpair,
    evaluate_symbolicRepeatedRootCertificate]
  have hweights : weightsOfCoordinates (inverseMassCoordinates m) =
      fun i ↦ (m.mass i)⁻¹ :=
    weightsOfCoordinates_inverseMassCoordinates m
  rw [hweights]
  exact hresultant

/-- Existence form of the supported-witness reduction. -/
theorem twoSiteRepeatedRootSlicePolynomial_ne_zero_of_exists_supported_simple
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (hwitness : ∃ pair : Real × Real,
      pair ∈ iidMassPairSupport ∧
      SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)) :
    twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂ ≠ 0 := by
  obtain ⟨pair, hpair, hsimple⟩ := hwitness
  intro hzero
  have hne := twoSiteRepeatedRootSlicePolynomial_eval_ne_zero_of_simple
    fixed hsite hpair hsimple
  apply hne
  rw [hzero]
  simp

end

end ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing
