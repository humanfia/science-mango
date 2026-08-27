import ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit
import ArchonPhysics.OrderedRankThresholdCountIdentity
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Graph identification and uniqueness of rank-frequency marked limits

For a scalar integrated density of states `F`, the decreasing normalized
rank carried by a mode of frequency `omega` must lie on the graph

`rank = 1 - F (omega ^ 2)`.

This module proves the exact finite-volume version using the empirical
spectral threshold count, then proves a closed graph theorem for weak limits.
The limit theorem assumes uniform convergence of the empirical scalar CDFs
to a continuous `F`.  Its proof uses a bounded continuous graph-defect
observable, so it applies directly to the weak topology on probability
measures.

Finally, a measure concentrated on this graph is reconstructed exactly from
its Euclidean frequency marginal.  Hence graph concentration together with
the already identified frequency marginal implies uniqueness of the full
rank-frequency marked cluster point.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalRankFrequencyMarkedGraphLimit

open ArchonPhysics
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedMarginalLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedRankThresholdCountIdentity
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassAcousticCountingComparison
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## Closed graph and a bounded defect observable -/

/-- Three-leg rank-frequency graph associated with a scalar IDS `F`. -/
def rankFrequencyTripleGraph (F : Real -> Real) :
    Set (Fin 3 -> RankFrequencyMark) :=
  {marks | forall r, (marks r).1 = 1 - F ((marks r).2 ^ 2)}

/-- Bounded violation of one leg of the rank-frequency graph.  Clipping by
one makes this a valid global bounded continuous weak-convergence test. -/
def rankFrequencyGraphDefect (F : Real -> Real) (r : Fin 3)
    (marks : Fin 3 -> RankFrequencyMark) : Real :=
  min 1 |(marks r).1 - (1 - F ((marks r).2 ^ 2))|

theorem continuous_rankFrequencyGraphDefect {F : Real -> Real}
    (hF : Continuous F) (r : Fin 3) :
    Continuous (rankFrequencyGraphDefect F r) := by
  unfold rankFrequencyGraphDefect
  fun_prop

theorem rankFrequencyGraphDefect_nonneg (F : Real -> Real) (r : Fin 3)
    (marks : Fin 3 -> RankFrequencyMark) :
    0 <= rankFrequencyGraphDefect F r marks := by
  unfold rankFrequencyGraphDefect
  exact le_min zero_le_one (abs_nonneg _)

theorem rankFrequencyGraphDefect_le_one (F : Real -> Real) (r : Fin 3)
    (marks : Fin 3 -> RankFrequencyMark) :
    rankFrequencyGraphDefect F r marks <= 1 :=
  min_le_left _ _

/-- Bundled bounded continuous graph-defect test. -/
def rankFrequencyGraphDefectBCF (F : Real -> Real) (hF : Continuous F)
    (r : Fin 3) :
    BoundedContinuousFunction (Fin 3 -> RankFrequencyMark) Real :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (rankFrequencyGraphDefect F r)
    (continuous_rankFrequencyGraphDefect hF r) 1 (fun marks => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (rankFrequencyGraphDefect_nonneg F r marks)]
      exact rankFrequencyGraphDefect_le_one F r marks)

@[simp] theorem rankFrequencyGraphDefectBCF_apply
    (F : Real -> Real) (hF : Continuous F) (r : Fin 3)
    (marks : Fin 3 -> RankFrequencyMark) :
    rankFrequencyGraphDefectBCF F hF r marks =
      rankFrequencyGraphDefect F r marks := by
  rfl

theorem rankFrequencyGraphDefect_eq_zero_iff
    (F : Real -> Real) (r : Fin 3)
    (marks : Fin 3 -> RankFrequencyMark) :
    rankFrequencyGraphDefect F r marks = 0 <->
      (marks r).1 = 1 - F ((marks r).2 ^ 2) := by
  unfold rankFrequencyGraphDefect
  constructor
  · intro hzero
    have habs : |(marks r).1 - (1 - F ((marks r).2 ^ 2))| = 0 := by
      by_contra hne
      have hpos : 0 < |(marks r).1 - (1 - F ((marks r).2 ^ 2))| :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
      have hmin :
          0 < min 1 |(marks r).1 - (1 - F ((marks r).2 ^ 2))| :=
        lt_min one_pos hpos
      linarith
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · intro heq
    simp [heq]

/-- Continuity of `F` makes the three-leg rank-frequency graph closed. -/
theorem isClosed_rankFrequencyTripleGraph {F : Real -> Real}
    (hF : Continuous F) : IsClosed (rankFrequencyTripleGraph F) := by
  have hgraph : rankFrequencyTripleGraph F = ⋂ r : Fin 3,
      {marks : Fin 3 -> RankFrequencyMark |
        (marks r).1 = 1 - F ((marks r).2 ^ 2)} := by
    ext marks
    simp [rankFrequencyTripleGraph]
  rw [hgraph]
  apply isClosed_iInter
  intro r
  exact isClosed_eq
    (by fun_prop : Continuous fun marks : Fin 3 -> RankFrequencyMark =>
      (marks r).1)
    (by fun_prop : Continuous fun marks : Fin 3 -> RankFrequencyMark =>
      1 - F ((marks r).2 ^ 2))

/-! ## Abstract uniform-CDF weak-limit bridge -/

theorem rankFrequencyGraphDefect_lt_of_exact_of_uniform
    {Fn F : Real -> Real} {epsilon : Real} (r : Fin 3)
    (marks : Fin 3 -> RankFrequencyMark)
    (hexact : (marks r).1 = 1 - Fn ((marks r).2 ^ 2))
    (huniform : forall E, dist (F E) (Fn E) < epsilon) :
    rankFrequencyGraphDefect F r marks < epsilon := by
  unfold rankFrequencyGraphDefect
  calc
    min 1 |(marks r).1 - (1 - F ((marks r).2 ^ 2))| <=
        |(marks r).1 - (1 - F ((marks r).2 ^ 2))| := min_le_right _ _
    _ = dist (F ((marks r).2 ^ 2)) (Fn ((marks r).2 ^ 2)) := by
      rw [hexact, Real.dist_eq]
      congr 1
      ring
    _ < epsilon := huniform _

/-- Uniform convergence of the scalar CDFs forces every leg's bounded graph
defect integral to vanish along any exactly graph-supported sequence. -/
theorem integral_rankFrequencyGraphDefect_tendsto_zero
    (mu : Nat -> ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (Fn : Nat -> Real -> Real) (F : Real -> Real) (hF : Continuous F)
    (huniform : TendstoUniformly Fn F atTop)
    (hexact : forall j,
      ∀ᵐ marks ∂(mu j : Measure (Fin 3 -> RankFrequencyMark)),
        marks ∈ rankFrequencyTripleGraph (Fn j))
    (r : Fin 3) :
    Tendsto
      (fun j => ∫ marks, rankFrequencyGraphDefect F r marks
        ∂(mu j : Measure (Fin 3 -> RankFrequencyMark)))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have huniformHalf := (Metric.tendstoUniformly_iff.mp huniform)
    (epsilon / 2) (half_pos hepsilon)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 huniformHalf
  use N
  intro j hj
  have hjUniform := hN j hj
  have hpoint :
      ∀ᵐ marks ∂(mu j : Measure (Fin 3 -> RankFrequencyMark)),
        rankFrequencyGraphDefect F r marks <= epsilon / 2 := by
    filter_upwards [hexact j] with marks hmarks
    exact le_of_lt (rankFrequencyGraphDefect_lt_of_exact_of_uniform r marks
      (hmarks r) hjUniform)
  have hintegrable : Integrable (rankFrequencyGraphDefect F r)
      (mu j : Measure (Fin 3 -> RankFrequencyMark)) :=
    (BoundedContinuousFunction.integrable
      (mu j : Measure (Fin 3 -> RankFrequencyMark))
      (rankFrequencyGraphDefectBCF F hF r)).congr
        (Eventually.of_forall fun marks =>
          rankFrequencyGraphDefectBCF_apply F hF r marks)
  have hintegralNonneg :
      0 <= ∫ marks, rankFrequencyGraphDefect F r marks
        ∂(mu j : Measure (Fin 3 -> RankFrequencyMark)) :=
    integral_nonneg (fun marks => rankFrequencyGraphDefect_nonneg F r marks)
  have hintegralLe :
      (∫ marks, rankFrequencyGraphDefect F r marks
        ∂(mu j : Measure (Fin 3 -> RankFrequencyMark))) <= epsilon / 2 := by
    calc
      (∫ marks, rankFrequencyGraphDefect F r marks
          ∂(mu j : Measure (Fin 3 -> RankFrequencyMark))) <=
          ∫ _marks, epsilon / 2
            ∂(mu j : Measure (Fin 3 -> RankFrequencyMark)) :=
        integral_mono_ae hintegrable (integrable_const _) hpoint
      _ = epsilon / 2 := by simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hintegralNonneg]
  exact hintegralLe.trans_lt (half_lt_self hepsilon)

/-- Any weak limit of exactly empirical-graph-supported probability measures
is concentrated on the graph of the continuous uniform CDF limit. -/
theorem weakLimit_compl_rankFrequencyTripleGraph_eq_zero
    (mu : Nat -> ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (Fn : Nat -> Real -> Real) (F : Real -> Real) (hF : Continuous F)
    (huniform : TendstoUniformly Fn F atTop)
    (hexact : forall j,
      ∀ᵐ marks ∂(mu j : Measure (Fin 3 -> RankFrequencyMark)),
        marks ∈ rankFrequencyTripleGraph (Fn j))
    (hweak : Tendsto mu atTop (nhds target)) :
    (target : Measure (Fin 3 -> RankFrequencyMark))
      (rankFrequencyTripleGraph F)ᶜ = 0 := by
  have hintegralZero (r : Fin 3) :
      (∫ marks, rankFrequencyGraphDefect F r marks
        ∂(target : Measure (Fin 3 -> RankFrequencyMark))) = 0 := by
    have hweakIntegral :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak)
        (rankFrequencyGraphDefectBCF F hF r)
    have hzero := integral_rankFrequencyGraphDefect_tendsto_zero
      mu Fn F hF huniform hexact r
    exact tendsto_nhds_unique hweakIntegral hzero
  have haeLeg (r : Fin 3) :
      ∀ᵐ marks ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
        (marks r).1 = 1 - F ((marks r).2 ^ 2) := by
    have hintegrable : Integrable (rankFrequencyGraphDefect F r)
        (target : Measure (Fin 3 -> RankFrequencyMark)) :=
      (BoundedContinuousFunction.integrable
        (target : Measure (Fin 3 -> RankFrequencyMark))
        (rankFrequencyGraphDefectBCF F hF r)).congr
          (Eventually.of_forall fun marks =>
            rankFrequencyGraphDefectBCF_apply F hF r marks)
    have hdefectZero :
        rankFrequencyGraphDefect F r =ᵐ[(target : Measure
          (Fin 3 -> RankFrequencyMark))] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (rankFrequencyGraphDefect_nonneg F r) hintegrable).mp
          (hintegralZero r)
    filter_upwards [hdefectZero] with marks hmarks
    exact (rankFrequencyGraphDefect_eq_zero_iff F r marks).mp hmarks
  have haeGraph :
      ∀ᵐ marks ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
        marks ∈ rankFrequencyTripleGraph F := by
    change ∀ᵐ marks ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
      forall r : Fin 3, (marks r).1 = 1 - F ((marks r).2 ^ 2)
    rw [ae_all_iff]
    exact haeLeg
  exact ae_iff.mp haeGraph

/-! ## Reconstruction and uniqueness from the frequency marginal -/

/-- Deterministically attach the rank prescribed by `F` to a plain frequency
triple. -/
def liftRankFrequencyTriple (F : Real -> Real)
    (frequencies : Fin 3 -> Real) : Fin 3 -> RankFrequencyMark :=
  fun r => (1 - F ((frequencies r) ^ 2), frequencies r)

/-- Euclidean-frequency version of the deterministic graph lift. -/
def liftEuclideanRankFrequencyTriple (F : Real -> Real)
    (frequencies : EuclideanSpace Real (Fin 3)) :
    Fin 3 -> RankFrequencyMark :=
  liftRankFrequencyTriple F (euclideanFrequencyTripleToPlain frequencies)

theorem continuous_liftEuclideanRankFrequencyTriple {F : Real -> Real}
    (hF : Continuous F) :
    Continuous (liftEuclideanRankFrequencyTriple F) := by
  unfold liftEuclideanRankFrequencyTriple liftRankFrequencyTriple
  apply continuous_pi
  intro r
  have hfrequency :
      Continuous fun frequencies : EuclideanSpace Real (Fin 3) =>
        euclideanFrequencyTripleToPlain frequencies r :=
    (continuous_apply r).comp continuous_euclideanFrequencyTripleToPlain
  exact (continuous_const.sub (hF.comp (hfrequency.pow 2))).prodMk hfrequency

theorem measurable_liftEuclideanRankFrequencyTriple {F : Real -> Real}
    (hF : Continuous F) :
    Measurable (liftEuclideanRankFrequencyTriple F) :=
  (continuous_liftEuclideanRankFrequencyTriple hF).measurable

theorem liftEuclideanRankFrequencyTriple_forgetRankFrequencyTripleEuclidean_eq
    (F : Real -> Real) {marks : Fin 3 -> RankFrequencyMark}
    (hmarks : marks ∈ rankFrequencyTripleGraph F) :
    liftEuclideanRankFrequencyTriple F
      (forgetRankFrequencyTripleEuclidean marks) = marks := by
  funext r
  apply Prod.ext
  · exact (hmarks r).symm
  · rfl

/-- A graph-supported marked probability measure is exactly the graph lift
of its Euclidean frequency marginal. -/
theorem map_liftEuclidean_map_forgetEuclidean_eq_of_compl_graph_eq_zero
    (F : Real -> Real) (hF : Continuous F)
    (target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (hgraph : (target : Measure (Fin 3 -> RankFrequencyMark))
      (rankFrequencyTripleGraph F)ᶜ = 0) :
    ProbabilityMeasure.map
        (ProbabilityMeasure.map target
          measurable_forgetRankFrequencyTripleEuclidean.aemeasurable)
        (measurable_liftEuclideanRankFrequencyTriple hF).aemeasurable =
      target := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  calc
    Measure.map (liftEuclideanRankFrequencyTriple F)
        (Measure.map forgetRankFrequencyTripleEuclidean
          (target : Measure (Fin 3 -> RankFrequencyMark))) =
      Measure.map
        (liftEuclideanRankFrequencyTriple F ∘
          forgetRankFrequencyTripleEuclidean)
        (target : Measure (Fin 3 -> RankFrequencyMark)) :=
      AEMeasurable.map_map_of_aemeasurable
        (measurable_liftEuclideanRankFrequencyTriple hF).aemeasurable
        measurable_forgetRankFrequencyTripleEuclidean.aemeasurable
    _ = Measure.map id
        (target : Measure (Fin 3 -> RankFrequencyMark)) := by
      apply Measure.map_congr
      have haeGraph :
          ∀ᵐ marks ∂(target : Measure (Fin 3 -> RankFrequencyMark)),
            marks ∈ rankFrequencyTripleGraph F := ae_iff.mpr hgraph
      filter_upwards [haeGraph] with marks hmarks
      exact
        liftEuclideanRankFrequencyTriple_forgetRankFrequencyTripleEuclidean_eq
          F hmarks
    _ = (target : Measure (Fin 3 -> RankFrequencyMark)) := Measure.map_id

/-- Two measures concentrated on the same continuous IDS graph and having
the same Euclidean frequency marginal are equal. -/
theorem eq_of_compl_graph_eq_zero_of_map_forgetEuclidean_eq
    (F : Real -> Real) (hF : Continuous F)
    (target₁ target₂ : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (hgraph₁ : (target₁ : Measure (Fin 3 -> RankFrequencyMark))
      (rankFrequencyTripleGraph F)ᶜ = 0)
    (hgraph₂ : (target₂ : Measure (Fin 3 -> RankFrequencyMark))
      (rankFrequencyTripleGraph F)ᶜ = 0)
    (hmarginal : ProbabilityMeasure.map target₁
        measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
      ProbabilityMeasure.map target₂
        measurable_forgetRankFrequencyTripleEuclidean.aemeasurable) :
    target₁ = target₂ := by
  rw [← map_liftEuclidean_map_forgetEuclidean_eq_of_compl_graph_eq_zero
        F hF target₁ hgraph₁,
    ← map_liftEuclidean_map_forgetEuclidean_eq_of_compl_graph_eq_zero
        F hF target₂ hgraph₂,
    hmarginal]

/-! ## Exact finite-volume empirical graph and canonical limit theorem -/

/-- Complete finite-volume empirical scalar IDS of a harmonic realization. -/
def harmonicEmpiricalScalarIDS {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (E : Real) : Real :=
  (orderedEigenvalueThresholdCount (harmonicHermitian m) E : Real) /
    (N : Real)

/-- Every simple-spectrum marked mode triple lies exactly on the graph of
its realization's empirical scalar IDS. -/
theorem orderedRankFrequencyTriple_mem_harmonicEmpiricalScalarIDS_graph
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (modes : OrderedModeTriple N) :
    orderedRankFrequencyTriple m modes ∈
      rankFrequencyTripleGraph (harmonicEmpiricalScalarIDS m) := by
  intro r
  exact normalizedOrderedRank_eq_one_sub_harmonicThresholdCount
    m hsimple (modes r)

/-- The raw marked collision measure assigns zero mass off its exact
empirical rank-frequency graph. -/
theorem positiveWeightedRankFrequencyTripleMeasure_compl_empiricalGraph_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m)) :
    positiveWeightedRankFrequencyTripleMeasure m
      (rankFrequencyTripleGraph (harmonicEmpiricalScalarIDS m))ᶜ = 0 := by
  classical
  unfold positiveWeightedRankFrequencyTripleMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · rw [if_pos hpositive, Measure.smul_apply]
    simp [orderedRankFrequencyTriple_mem_harmonicEmpiricalScalarIDS_graph
      m hsimple modes]
  · rw [if_neg hpositive]
    rfl

/-- Per-site scaling retains exact empirical-graph concentration. -/
theorem canonicalRankFrequencyTriplePerSiteFiniteMeasure_compl_empiricalGraph_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble n omega :
      Measure (Fin 3 -> RankFrequencyMark))
      (rankFrequencyTripleGraph
        (harmonicEmpiricalScalarIDS
          (ensemble.restrictPositiveMass (N := n + 2) omega)))ᶜ = 0 := by
  unfold canonicalRankFrequencyTriplePerSiteFiniteMeasure
  rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply]
  change _ * positiveWeightedRankFrequencyTripleMeasure
      (ensemble.restrictPositiveMass (N := n + 2) omega)
      (rankFrequencyTripleGraph
        (harmonicEmpiricalScalarIDS
          (ensemble.restrictPositiveMass (N := n + 2) omega)))ᶜ = 0
  rw [positiveWeightedRankFrequencyTripleMeasure_compl_empiricalGraph_eq_zero
    (ensemble.restrictPositiveMass (N := n + 2) omega) hsimple]
  simp

/-- Nonzero probability normalization retains exact empirical-graph
concentration. -/
theorem canonicalNormalizedRankFrequencyMarkedMeasure_compl_empiricalGraph_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega)
    (hN : 3 <= n + 2)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    (canonicalNormalizedRankFrequencyMarkedMeasure ensemble n omega :
      Measure (Fin 3 -> RankFrequencyMark))
      (rankFrequencyTripleGraph
        (harmonicEmpiricalScalarIDS
          (ensemble.restrictPositiveMass (N := n + 2) omega)))ᶜ = 0 := by
  have hmass := canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_ne_zero
    ensemble sign n omega hN hsimple
  have hmeasure : canonicalRankFrequencyTriplePerSiteFiniteMeasure
      ensemble n omega ≠ 0 :=
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure
      ensemble n omega).mass_nonzero_iff.mp hmass
  unfold canonicalNormalizedRankFrequencyMarkedMeasure
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hmeasure,
    Measure.smul_apply]
  rw [canonicalRankFrequencyTriplePerSiteFiniteMeasure_compl_empiricalGraph_eq_zero
    ensemble n omega hsimple]
  simp

theorem canonicalNormalizedRankFrequencyMarkedMeasure_ae_mem_empiricalGraph
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) (n : Nat) (omega : Omega)
    (hN : 3 <= n + 2)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    ∀ᵐ marks ∂(canonicalNormalizedRankFrequencyMarkedMeasure ensemble n omega :
        Measure (Fin 3 -> RankFrequencyMark)),
      marks ∈ rankFrequencyTripleGraph
        (harmonicEmpiricalScalarIDS
          (ensemble.restrictPositiveMass (N := n + 2) omega)) := by
  rw [ae_iff]
  exact
    canonicalNormalizedRankFrequencyMarkedMeasure_compl_empiricalGraph_eq_zero
      ensemble sign n omega hN hsimple

/-- Canonical physical specialization of the abstract graph-limit theorem.
The only asymptotic spectral input is uniform convergence of the empirical
scalar IDS to a continuous limit. -/
theorem canonicalMarkedWeakLimit_compl_rankFrequencyTripleGraph_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    (size : Nat -> Nat) (omega : Nat -> Omega)
    (sign : Fin 3 -> InteractionSign)
    (target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (F : Real -> Real) (hF : Continuous F)
    (hN : forall j, 3 <= size j + 2)
    (hsimple : forall j, SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := size j + 2) (omega j))))
    (huniform : TendstoUniformly
      (fun j => harmonicEmpiricalScalarIDS
        (ensemble.restrictPositiveMass (N := size j + 2) (omega j)))
      F atTop)
    (hweak : Tendsto
      (fun j => canonicalNormalizedRankFrequencyMarkedMeasure
        ensemble (size j) (omega j))
      atTop (nhds target)) :
    (target : Measure (Fin 3 -> RankFrequencyMark))
      (rankFrequencyTripleGraph F)ᶜ = 0 := by
  exact weakLimit_compl_rankFrequencyTripleGraph_eq_zero
    (fun j => canonicalNormalizedRankFrequencyMarkedMeasure
      ensemble (size j) (omega j))
    target
    (fun j => harmonicEmpiricalScalarIDS
      (ensemble.restrictPositiveMass (N := size j + 2) (omega j)))
    F hF huniform
    (fun j =>
      canonicalNormalizedRankFrequencyMarkedMeasure_ae_mem_empiricalGraph
        ensemble sign (size j) (omega j) (hN j) (hsimple j))
    hweak

/-- Under the uniform empirical-IDS input, a canonical marked weak limit is
the deterministic graph lift of whichever Euclidean frequency marginal it
has. -/
theorem canonicalMarkedWeakLimit_eq_lift_of_uniformEmpiricalIDS
    (ensemble : IIDMassPhaseEnsemble Omega)
    (size : Nat -> Nat) (omega : Nat -> Omega)
    (sign : Fin 3 -> InteractionSign)
    (target : ProbabilityMeasure (Fin 3 -> RankFrequencyMark))
    (frequencyTarget : ProbabilityMeasure (EuclideanSpace Real (Fin 3)))
    (F : Real -> Real) (hF : Continuous F)
    (hN : forall j, 3 <= size j + 2)
    (hsimple : forall j, SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := size j + 2) (omega j))))
    (huniform : TendstoUniformly
      (fun j => harmonicEmpiricalScalarIDS
        (ensemble.restrictPositiveMass (N := size j + 2) (omega j)))
      F atTop)
    (hweak : Tendsto
      (fun j => canonicalNormalizedRankFrequencyMarkedMeasure
        ensemble (size j) (omega j))
      atTop (nhds target))
    (hmarginal : ProbabilityMeasure.map target
        measurable_forgetRankFrequencyTripleEuclidean.aemeasurable =
      frequencyTarget) :
    target = ProbabilityMeasure.map frequencyTarget
      (measurable_liftEuclideanRankFrequencyTriple hF).aemeasurable := by
  have hgraph :=
    canonicalMarkedWeakLimit_compl_rankFrequencyTripleGraph_eq_zero
      ensemble size omega sign target F hF hN hsimple huniform hweak
  have hreconstruct :=
    map_liftEuclidean_map_forgetEuclidean_eq_of_compl_graph_eq_zero
      F hF target hgraph
  rw [hmarginal] at hreconstruct
  exact hreconstruct.symm

end
end ArchonPhysics.CanonicalRankFrequencyMarkedGraphLimit
