import ArchonPhysics.ChildRepeatedAnnealedWeakTestCenter
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Conditional inverse-volume self-averaging for child weak tests

This module closes the concentration and Borel--Cantelli part of the
child-repeated route from one explicit model input: changing one of the
`N = n+2` masses changes the normalized weak test by at most `K/N`.

The input is not asserted for the random lattice.  The earlier unconditional
range-only estimate has sensitivity one and variance proxy `N/4`; it cannot
be substituted for the inverse-volume hypothesis below.
-/

open scoped ENNReal NNReal BoundedContinuousFunction

namespace ArchonPhysics.ChildRepeatedInverseSensitivitySelfAveraging

open ArchonPhysics
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.ChildRepeatedAnnealedWeakTestCenter
open ArchonPhysics.ChildRepeatedBoundedDifferenceAudit
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.FiniteProductBoundedDifferences
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory ProbabilityTheory Set Topology

noncomputable section

/-- The sharp McDiarmid proxy corresponding to `K/N` sensitivity in each of
`N = n+2` coordinates. -/
def childRepeatedInverseSensitivityParameter (n : Nat) (K : NNReal) : NNReal :=
  K ^ 2 / (4 * ((n + 2 : Nat) : NNReal))

theorem varianceProxy_childRepeated_inverseSensitivity
    (n : Nat) (K : NNReal) :
    varianceProxy
        (fun _ : Fin (n + 2) ↦ K / ((n + 2 : Nat) : NNReal)) =
      childRepeatedInverseSensitivityParameter n K := by
  apply NNReal.eq
  simp [varianceProxy, childRepeatedInverseSensitivityParameter,
    Finset.sum_const, nsmul_eq_mul]
  have hN : (((n + 2 : Nat) : Real)) ≠ 0 := by positivity
  field_simp
  ring

/-- Product-space MGF estimate centered at the exact canonical annealed weak
test.  Both range normalization and inverse-volume sensitivity are explicit
model hypotheses. -/
theorem finChildRepeatedReducedRawTest_hasSubgaussianMGF_of_inverseSensitivity
    (n : Nat) (test : (Real × Real) →ᵇ NNReal) (K : NNReal)
    (hrange : ∀ x, finChildRepeatedReducedRawTest n test x ∈ Set.Icc 0 1)
    (hsensitivity : HasFinBoundedDifferences
      (finChildRepeatedReducedRawTest n test)
      (fun _ : Fin (n + 2) ↦ K / ((n + 2 : Nat) : NNReal))) :
    HasSubgaussianMGF
      (fun x ↦ finChildRepeatedReducedRawTest n test x -
        ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN test : Real))
      (childRepeatedInverseSensitivityParameter n K)
      (Measure.pi fun _ : Fin (n + 2) ↦ massCoordinateLaw) := by
  have h := hasSubgaussianMGF_finitePi_of_boundedDifferences
    massCoordinateLaw (n + 2)
    (finChildRepeatedReducedRawTest n test)
    (fun _ : Fin (n + 2) ↦ K / ((n + 2 : Nat) : NNReal))
    (measurable_finChildRepeatedReducedRawTest n test)
    hrange hsensitivity
  rw [varianceProxy_childRepeated_inverseSensitivity,
    integral_finChildRepeatedReducedRawTest_eq_annealed_testAgainstNN] at h
  exact h

/-- The same actual weak test, now represented on the common canonical
infinite-product sample space. -/
def canonicalChildRepeatedReducedRawTest
    (n : Nat) (test : (Real × Real) →ᵇ NNReal)
    (omega : RandomEnsemble.SampleSpace) : Real :=
  finChildRepeatedReducedRawTest n test
    (canonicalChildRepeatedFinMassVector n omega)

theorem measurable_canonicalChildRepeatedReducedRawTest
    (n : Nat) (test : (Real × Real) →ᵇ NNReal) :
    Measurable (canonicalChildRepeatedReducedRawTest n test) :=
  (measurable_finChildRepeatedReducedRawTest n test).comp
    (measurable_canonicalChildRepeatedFinMassVector n)

theorem canonicalChildRepeatedReducedRawTest_eq_testAgainstNN
    (n : Nat) (test : (Real × Real) →ᵇ NNReal)
    (omega : RandomEnsemble.SampleSpace) :
    canonicalChildRepeatedReducedRawTest n test omega =
      (((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
          canonicalIIDMassPhaseEnsemble n omega).map
        CanonicalRankFrequencyMarkedMeasure.forgetRankFrequencyTriple).map
          ChildRepeatedDiagonalHybridKernel.childRepeatedFrequencyProjection).testAgainstNN test := by
  unfold canonicalChildRepeatedReducedRawTest
  rw [finChildRepeatedReducedRawTest_eq_testAgainstNN]
  rw [finChildRepeatedReducedFiniteMeasure_canonicalFinMassVector]

/-- Transport the sharp product-space certificate to the common canonical
sample space needed by Borel--Cantelli. -/
theorem canonicalChildRepeatedReducedRawTest_hasSubgaussianMGF_of_inverseSensitivity
    (n : Nat) (test : (Real × Real) →ᵇ NNReal) (K : NNReal)
    (hrange : ∀ x, finChildRepeatedReducedRawTest n test x ∈ Set.Icc 0 1)
    (hsensitivity : HasFinBoundedDifferences
      (finChildRepeatedReducedRawTest n test)
      (fun _ : Fin (n + 2) ↦ K / ((n + 2 : Nat) : NNReal))) :
    HasSubgaussianMGF
      (fun omega ↦ canonicalChildRepeatedReducedRawTest n test omega -
        ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN test : Real))
      (childRepeatedInverseSensitivityParameter n K) canonicalLaw := by
  have hproduct : HasSubgaussianMGF
      (fun x ↦ finChildRepeatedReducedRawTest n test x -
        ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN test : Real))
      (childRepeatedInverseSensitivityParameter n K)
      (canonicalLaw.map (canonicalChildRepeatedFinMassVector n)) := by
    rw [(canonicalChildRepeatedFinMassVector_hasLaw n).map_eq]
    exact
      finChildRepeatedReducedRawTest_hasSubgaussianMGF_of_inverseSensitivity
        n test K hrange hsensitivity
  have htransport := HasSubgaussianMGF.of_map
    (measurable_canonicalChildRepeatedFinMassVector n).aemeasurable hproduct
  simpa [canonicalChildRepeatedReducedRawTest, Function.comp_def] using htransport

/-- Sharp upper tail under the missing `K/N` sensitivity input. -/
theorem canonicalChildRepeatedReducedRawTest_inverseSensitivity_upperTail
    (n : Nat) (test : (Real × Real) →ᵇ NNReal) (K : NNReal)
    (hK : 0 < K)
    (hrange : ∀ x, finChildRepeatedReducedRawTest n test x ∈ Set.Icc 0 1)
    (hsensitivity : HasFinBoundedDifferences
      (finChildRepeatedReducedRawTest n test)
      (fun _ : Fin (n + 2) ↦ K / ((n + 2 : Nat) : NNReal)))
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    canonicalLaw.real
        {omega | epsilon ≤
          canonicalChildRepeatedReducedRawTest n test omega -
            ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN test : Real)} ≤
      Real.exp
        (-2 * ((n + 2 : Nat) : Real) * epsilon ^ 2 / (K : Real) ^ 2) := by
  have htail :=
    (canonicalChildRepeatedReducedRawTest_hasSubgaussianMGF_of_inverseSensitivity
      n test K hrange hsensitivity).measure_ge_le hepsilon
  have hN : (((n + 2 : Nat) : Real)) ≠ 0 := by positivity
  have hKR : (K : Real) ≠ 0 := by exact_mod_cast hK.ne'
  convert htail using 1
  congr 1
  simp only [childRepeatedInverseSensitivityParameter, NNReal.coe_div,
    NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast]
  field_simp
  ring

/-- Two-sided exponential concentration under inverse-volume sensitivity. -/
theorem canonicalChildRepeatedReducedRawTest_inverseSensitivity_twoSided
    (n : Nat) (test : (Real × Real) →ᵇ NNReal) (K : NNReal)
    (hK : 0 < K)
    (hrange : ∀ x, finChildRepeatedReducedRawTest n test x ∈ Set.Icc 0 1)
    (hsensitivity : HasFinBoundedDifferences
      (finChildRepeatedReducedRawTest n test)
      (fun _ : Fin (n + 2) ↦ K / ((n + 2 : Nat) : NNReal)))
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    canonicalLaw.real
        {omega | epsilon ≤
          |canonicalChildRepeatedReducedRawTest n test omega -
            ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN test : Real)|} ≤
      2 * Real.exp
        (-2 * ((n + 2 : Nat) : Real) * epsilon ^ 2 / (K : Real) ^ 2) := by
  let X : RandomEnsemble.SampleSpace → Real := fun omega ↦
    canonicalChildRepeatedReducedRawTest n test omega -
      ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN test : Real)
  have hset : {omega | epsilon ≤ |X omega|} =
      {omega | epsilon ≤ X omega} ∪ {omega | epsilon ≤ -X omega} := by
    ext omega
    change epsilon ≤ |X omega| ↔ epsilon ≤ X omega ∨ epsilon ≤ -X omega
    exact le_abs
  rw [show {omega | epsilon ≤
        |canonicalChildRepeatedReducedRawTest n test omega -
          ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN test : Real)|} =
      {omega | epsilon ≤ |X omega|} by rfl, hset]
  calc
    canonicalLaw.real
        ({omega | epsilon ≤ X omega} ∪ {omega | epsilon ≤ -X omega}) ≤
      canonicalLaw.real {omega | epsilon ≤ X omega} +
        canonicalLaw.real {omega | epsilon ≤ -X omega} :=
      measureReal_union_le _ _
    _ ≤ Real.exp
          (-2 * ((n + 2 : Nat) : Real) * epsilon ^ 2 / (K : Real) ^ 2) +
        Real.exp
          (-2 * ((n + 2 : Nat) : Real) * epsilon ^ 2 / (K : Real) ^ 2) := by
      apply add_le_add
      · simpa [X] using
          canonicalChildRepeatedReducedRawTest_inverseSensitivity_upperTail
            n test K hK hrange hsensitivity hepsilon
      · have htail :=
          (canonicalChildRepeatedReducedRawTest_hasSubgaussianMGF_of_inverseSensitivity
            n test K hrange hsensitivity).neg.measure_ge_le hepsilon
        have hN : (((n + 2 : Nat) : Real)) ≠ 0 := by positivity
        have hKR : (K : Real) ≠ 0 := by exact_mod_cast hK.ne'
        have hexp :
            Real.exp (-epsilon ^ 2 /
              (2 * (childRepeatedInverseSensitivityParameter n K : Real))) =
              Real.exp (-2 * ((n + 2 : Nat) : Real) * epsilon ^ 2 /
                (K : Real) ^ 2) := by
          congr 1
          simp only [childRepeatedInverseSensitivityParameter, NNReal.coe_div,
            NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_ofNat,
            NNReal.coe_natCast]
          field_simp
          ring
        rw [hexp] at htail
        simpa [X] using htail
    _ = 2 * Real.exp
          (-2 * ((n + 2 : Nat) : Real) * epsilon ^ 2 / (K : Real) ^ 2) := by
      ring

/-- Under a uniform inverse-volume sensitivity theorem, the child weak test
self-averages almost surely around its genuine annealed finite-volume value.
This is the precise Borel--Cantelli endpoint required by the cluster bridge. -/
theorem canonicalChildRepeatedReducedRawTest_tendsto_annealed_ae_of_inverseSensitivity
    (test : (Real × Real) →ᵇ NNReal) (K : NNReal) (hK : 0 < K)
    (hrange : ∀ n x,
      finChildRepeatedReducedRawTest n test x ∈ Set.Icc 0 1)
    (hsensitivity : ∀ n, HasFinBoundedDifferences
      (finChildRepeatedReducedRawTest n test)
      (fun _ : Fin (n + 2) ↦ K / ((n + 2 : Nat) : NNReal))) :
    ∀ᵐ omega ∂canonicalLaw,
      Tendsto
        (fun n ↦
          |canonicalChildRepeatedReducedRawTest n test omega -
            ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN test : Real)|)
        atTop (nhds 0) := by
  have hsummable (epsilon : Real) (hepsilon : 0 < epsilon) :
      (∑' n : Nat, canonicalLaw
        {omega | epsilon ≤
          |canonicalChildRepeatedReducedRawTest n test omega -
            ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN test : Real)|}) ≠ ∞ := by
    let c : Real := -2 * epsilon ^ 2 / (K : Real) ^ 2
    have hc : c < 0 := by
      have hKR : 0 < (K : Real) := by exact_mod_cast hK
      dsimp [c]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hepsilon))
        (sq_pos_of_pos hKR)
    have hbase : Summable (fun n : Nat ↦ Real.exp ((n : Real) * c)) :=
      Real.summable_exp_nat_mul_iff.mpr hc
    have hboundSummable : Summable (fun n : Nat ↦
        2 * Real.exp
          (-2 * ((n + 2 : Nat) : Real) * epsilon ^ 2 /
            (K : Real) ^ 2)) := by
      have hscaled := hbase.mul_left (2 * Real.exp (2 * c))
      apply hscaled.congr
      intro n
      rw [show -2 * ((n + 2 : Nat) : Real) * epsilon ^ 2 /
          (K : Real) ^ 2 = ((n : Real) + 2) * c by
        simp only [Nat.cast_add, Nat.cast_ofNat]
        dsimp [c]
        ring]
      rw [add_mul, Real.exp_add]
      ring
    have hmeasureBound : ∀ n : Nat,
        canonicalLaw
            {omega | epsilon ≤
              |canonicalChildRepeatedReducedRawTest n test omega -
                ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN test : Real)|} ≤
          ENNReal.ofReal
            (2 * Real.exp
              (-2 * ((n + 2 : Nat) : Real) * epsilon ^ 2 /
                (K : Real) ^ 2)) := by
      intro n
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal
        (canonicalChildRepeatedReducedRawTest_inverseSensitivity_twoSided
          n test K hK (hrange n) (hsensitivity n) hepsilon.le)
    exact ((ENNReal.tsum_le_tsum hmeasureBound).trans_lt
      hboundSummable.tsum_ofReal_lt_top).ne
  have heventually (epsilon : Real) (hepsilon : 0 < epsilon) :
      ∀ᵐ omega ∂canonicalLaw, ∀ᶠ n : Nat in atTop,
        |canonicalChildRepeatedReducedRawTest n test omega -
          ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN test : Real)| < epsilon := by
    have hbc := ae_eventually_notMem (hsummable epsilon hepsilon)
    filter_upwards [hbc] with omega homega
    filter_upwards [homega] with n hn
    simpa only [Set.mem_ofPred_eq, not_le] using hn
  have hgrid : ∀ k : Nat, ∀ᵐ omega ∂canonicalLaw, ∀ᶠ n : Nat in atTop,
      |canonicalChildRepeatedReducedRawTest n test omega -
        ((canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).testAgainstNN test : Real)| <
        1 / ((k + 1 : Nat) : Real) := by
    intro k
    apply heventually
    positivity
  filter_upwards [ae_all_iff.mpr hgrid] with omega homega
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hepsilon
  have hk' : 1 / ((k + 1 : Nat) : Real) < epsilon := by
    simpa only [Nat.cast_add, Nat.cast_one] using hk
  have hkEventually := homega k
  rw [eventually_atTop] at hkEventually
  obtain ⟨N, hN⟩ := hkEventually
  refine ⟨N, fun n hn ↦ ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_abs] using (hN n hn).trans hk'

end

end ArchonPhysics.ChildRepeatedInverseSensitivitySelfAveraging
