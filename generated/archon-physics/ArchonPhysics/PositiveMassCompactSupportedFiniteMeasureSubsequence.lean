import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Sequential compactness for positive-mass finite measures

When finite measures have one compact support and their masses converge to a
strictly positive value, their probability normalizations form a tight
family.  Prokhorov compactness of that probability family and convergence of
the masses then recover a weakly convergent finite-measure subsequence.
-/

open scoped Topology

namespace ArchonPhysics.PositiveMassCompactSupportedFiniteMeasureSubsequence

open Filter MeasureTheory Set Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [Nonempty X]
  [T2Space X] [BorelSpace X]
  [FirstCountableTopology (ProbabilityMeasure X)]

/-- Common compact support and convergence to a positive total mass give a
weakly convergent strictly increasing subsequence of finite measures. -/
theorem exists_weaklyConvergent_subsequence_of_compactSupport_of_mass_tendsto_pos
    (mu : Nat -> FiniteMeasure X) (massLimit : NNReal)
    (hmassLimit : 0 < massLimit) (K : Set X) (hK : IsCompact K)
    (hmass : Tendsto (fun n => (mu n).mass) atTop (nhds massLimit))
    (hsupport : forall n, (mu n : Measure X) Kᶜ = 0) :
    exists target : FiniteMeasure X,
      exists subsequence : Nat -> Nat,
        StrictMono subsequence /\
          Tendsto (fun j => mu (subsequence j)) atTop (nhds target) := by
  have hmassPosEventually : ∀ᶠ n in atTop, 0 < (mu n).mass :=
    hmass.eventually (Ioi_mem_nhds hmassLimit)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hmassPosEventually
  let normalized : Nat -> ProbabilityMeasure X := fun j => (mu (N + j)).normalize
  have hnonzero : forall j, mu (N + j) ≠ 0 := by
    intro j
    exact (mu (N + j)).mass_nonzero_iff.mp
      (ne_of_gt (hN (N + j) (Nat.le_add_right N j)))
  have hnormalizedSupport : forall j,
      (normalized j : Measure X) Kᶜ = 0 := by
    intro j
    unfold normalized
    rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ (hnonzero j),
      Measure.smul_apply]
    rw [hsupport]
    simp
  have hset :
      {((nu : ProbabilityMeasure X) : Measure X) |
        nu ∈ Set.range normalized} =
      Set.range (fun j => (normalized j : Measure X)) := by
    ext measure
    simp
  have htight : IsTightMeasureSet
      {((nu : ProbabilityMeasure X) : Measure X) |
        nu ∈ Set.range normalized} := by
    rw [hset, isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro epsilon hepsilon
    refine ⟨K, hK, ?_⟩
    intro measure hmeasure
    rcases hmeasure with ⟨j, rfl⟩
    rw [hnormalizedSupport j]
    exact hepsilon.le
  have hcompact : IsCompact (closure (Set.range normalized)) :=
    isCompact_closure_of_isTightMeasureSet htight
  have hmem : forall j, normalized j ∈ closure (Set.range normalized) :=
    fun j => subset_closure (Set.mem_range_self j)
  obtain ⟨targetProbability, _htarget, sub, hsub, hnormalized⟩ :=
    hcompact.tendsto_subseq hmem
  let subsequence : Nat -> Nat := fun j => N + sub j
  have hsubsequence : StrictMono subsequence := by
    intro i j hij
    exact Nat.add_lt_add_left (hsub hij) N
  let target : FiniteMeasure X :=
    massLimit • targetProbability.toFiniteMeasure
  have htargetMass : target.mass = massLimit := by
    unfold target FiniteMeasure.mass
    rw [FiniteMeasure.smul_apply]
    simp
  have htargetNonzero : target ≠ 0 := by
    apply target.mass_nonzero_iff.mp
    rw [htargetMass]
    exact hmassLimit.ne'
  have htargetNormalize : target.normalize = targetProbability := by
    apply ProbabilityMeasure.eq_of_forall_apply_eq
    intro s hs
    rw [target.normalize_eq_of_nonzero htargetNonzero]
    rw [htargetMass]
    unfold target
    rw [FiniteMeasure.smul_apply]
    simp [ne_of_gt hmassLimit]
  have hnormalizeSub : Tendsto
      (fun j => (mu (subsequence j)).normalize)
      atTop (nhds target.normalize) := by
    rw [htargetNormalize]
    change Tendsto (normalized ∘ sub) atTop (nhds targetProbability)
    exact hnormalized
  have hsubsequenceAtTop : Tendsto subsequence atTop atTop :=
    hsubsequence.tendsto_atTop
  have hmassSub : Tendsto (fun j => (mu (subsequence j)).mass)
      atTop (nhds target.mass) := by
    rw [htargetMass]
    exact hmass.comp hsubsequenceAtTop
  have hmeasureSub : Tendsto (fun j => mu (subsequence j))
      atTop (nhds target) :=
    FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
      hnormalizeSub hmassSub
  exact ⟨target, subsequence, hsubsequence, hmeasureSub⟩

end

end ArchonPhysics.PositiveMassCompactSupportedFiniteMeasureSubsequence
