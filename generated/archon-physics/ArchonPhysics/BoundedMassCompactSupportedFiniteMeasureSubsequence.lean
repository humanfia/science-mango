import ArchonPhysics.PositiveMassCompactSupportedFiniteMeasureSubsequence

/-!
# Sequential compactness for bounded compactly supported finite measures

The positive-mass compactness theorem is extended to sequences whose cluster
mass may be zero.  First extract a convergent mass subsequence in a compact
interval.  A zero mass limit forces weak convergence to the zero measure;
a positive mass limit is handled by probability normalization and Prokhorov
compactness through the existing theorem.
-/

open scoped Topology

namespace ArchonPhysics.BoundedMassCompactSupportedFiniteMeasureSubsequence

open ArchonPhysics.PositiveMassCompactSupportedFiniteMeasureSubsequence
open Filter MeasureTheory Set Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [Nonempty X]
  [T2Space X] [BorelSpace X]
  [FirstCountableTopology (ProbabilityMeasure X)]

/-- Common compact support and a uniform mass ceiling give a weakly
convergent strictly increasing subsequence, including when the limiting mass
is zero. -/
theorem exists_weaklyConvergent_subsequence_of_compactSupport_of_mass_le
    (mu : Nat -> FiniteMeasure X) (massCeiling : NNReal)
    (K : Set X) (hK : IsCompact K)
    (hmass : forall n, (mu n).mass <= massCeiling)
    (hsupport : forall n, (mu n : Measure X) Kᶜ = 0) :
    exists target : FiniteMeasure X,
      exists subsequence : Nat -> Nat,
        StrictMono subsequence /\
          Tendsto (fun j => mu (subsequence j)) atTop (nhds target) := by
  have hmassMem : forall n, (mu n).mass ∈ Set.Icc (0 : NNReal) massCeiling := by
    intro n
    exact ⟨bot_le, hmass n⟩
  obtain ⟨massLimit, _hmassLimitMem, massSubsequence,
      hmassSubsequenceMono, hmassLimit⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) massCeiling)).tendsto_subseq
      hmassMem
  by_cases hmassLimitZero : massLimit = 0
  · refine ⟨0, massSubsequence, hmassSubsequenceMono, ?_⟩
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    change Tendsto (fun j => (mu (massSubsequence j)).mass)
      atTop (nhds massLimit) at hmassLimit
    rw [hmassLimitZero] at hmassLimit
    exact hmassLimit
  · have hmassLimitPos : 0 < massLimit :=
      pos_iff_ne_zero.mpr hmassLimitZero
    obtain ⟨target, secondSubsequence, hsecondMono, hsecondLimit⟩ :=
      exists_weaklyConvergent_subsequence_of_compactSupport_of_mass_tendsto_pos
        (fun j => mu (massSubsequence j)) massLimit hmassLimitPos K hK
        hmassLimit
        (fun j => hsupport (massSubsequence j))
    refine ⟨target, massSubsequence ∘ secondSubsequence,
      hmassSubsequenceMono.comp hsecondMono, ?_⟩
    simpa only [Function.comp_apply] using hsecondLimit

end

end ArchonPhysics.BoundedMassCompactSupportedFiniteMeasureSubsequence
