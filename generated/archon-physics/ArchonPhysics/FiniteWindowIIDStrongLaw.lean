import ArchonPhysics.IIDMassStrongLaw
import Mathlib.Probability.IdentDistribIndep

/-!
# Strong laws for finite-window observables of iid masses

A measurable observable of a fixed finite mass window can be sampled on
non-overlapping blocks.  The resulting real random variables are iid, hence
their empirical averages obey the strong law.  Taking the finite intersection
over all residue offsets gives one almost-sure event on which every block
decomposition converges.

This is a probability/locality interface only.  In particular, it does not
identify a marked spectral kernel or assert a thermodynamic limit for one.
-/

namespace ArchonPhysics.FiniteWindowIIDStrongLaw

open ArchonPhysics
open Filter Function MeasureTheory ProbabilityTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The length-`W` mass window beginning at `W * k + offset`. -/
def massWindow (ensemble : IIDMassPhaseEnsemble Omega)
    (W offset k : Nat) (omega : Omega) : Fin W → Real :=
  fun j ↦ ensemble.mass (W * k + offset + j.val) omega

/-- A local observable evaluated on the `k`-th non-overlapping window in one
fixed residue class. -/
def windowObservable (ensemble : IIDMassPhaseEnsemble Omega)
    (W offset : Nat) (f : (Fin W → Real) → Real)
    (k : Nat) (omega : Omega) : Real :=
  f (massWindow ensemble W offset k omega)

/-- The natural-coordinate support of one mass window. -/
def massWindowIndexSet (W offset k : Nat) : Finset Nat :=
  Finset.Ico (W * k + offset) (W * k + offset + W)

/-- A window coordinate belongs to its natural-coordinate support. -/
theorem windowIndex_mem (W offset k : Nat) (j : Fin W) :
    W * k + offset + j.val ∈ massWindowIndexSet W offset k := by
  simp only [massWindowIndexSet, Finset.mem_Ico]
  omega

/-- Positive-width windows from distinct block indices have disjoint natural
coordinate supports. -/
theorem massWindowIndexSet_disjoint
    {W offset i k : Nat} (hik : i ≠ k) :
    Disjoint (massWindowIndexSet W offset i)
      (massWindowIndexSet W offset k) := by
  rw [Finset.disjoint_left]
  intro a hai hak
  simp only [massWindowIndexSet, Finset.mem_Ico] at hai hak
  rcases lt_or_gt_of_ne hik with hik | hki
  · have hstep : i + 1 ≤ k := Nat.succ_le_iff.mpr hik
    have hmul := Nat.mul_le_mul_left W hstep
    simp only [Nat.mul_add, Nat.mul_one] at hmul
    omega
  · have hstep : k + 1 ≤ i := Nat.succ_le_iff.mpr hki
    have hmul := Nat.mul_le_mul_left W hstep
    simp only [Nat.mul_add, Nat.mul_one] at hmul
    omega

/-- Extract the canonically ordered `Fin W` vector from a function indexed by
the finite support of one window. -/
def extractMassWindow (W offset k : Nat)
    (x : massWindowIndexSet W offset k → Real) : Fin W → Real :=
  fun j ↦ x ⟨W * k + offset + j.val, windowIndex_mem W offset k j⟩

theorem measurable_extractMassWindow (W offset k : Nat) :
    Measurable (extractMassWindow W offset k) := by
  exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply
    (⟨W * k + offset + j.val, windowIndex_mem W offset k j⟩ :
      massWindowIndexSet W offset k)

theorem measurable_massWindow
    (ensemble : IIDMassPhaseEnsemble Omega) (W offset k : Nat) :
    Measurable (massWindow ensemble W offset k) := by
  exact measurable_pi_lambda _ fun j ↦
    ensemble.mass_measurable (W * k + offset + j.val)

theorem measurable_windowObservable
    (ensemble : IIDMassPhaseEnsemble Omega) (W offset : Nat)
    (f : (Fin W → Real) → Real) (hf : Measurable f) (k : Nat) :
    Measurable (windowObservable ensemble W offset f k) := by
  exact hf.comp (measurable_massWindow ensemble W offset k)

/-- Every realized window lies pointwise in the frozen product support. -/
theorem massWindow_mem_support
    (ensemble : IIDMassPhaseEnsemble Omega) (W offset k : Nat)
    (omega : Omega) (j : Fin W) :
    massWindow ensemble W offset k omega j ∈
      RandomEnsemble.massSupport :=
  ensemble.mass_mem_support (W * k + offset + j.val) omega

/-- Every finite mass window has the same finite product law. -/
theorem massWindow_hasLaw
    (ensemble : IIDMassPhaseEnsemble Omega) (W offset k : Nat) :
    HasLaw (massWindow ensemble W offset k)
      (Measure.pi fun _ : Fin W ↦ RandomEnsemble.massCoordinateLaw)
      ensemble.probability := by
  have hinj : Injective (fun j : Fin W ↦ W * k + offset + j.val) := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel hij
  have hindep : iIndepFun
      (fun j : Fin W ↦
        ensemble.mass (W * k + offset + j.val))
      ensemble.probability :=
    ensemble.mass_iIndep.precomp hinj
  exact hindep.hasLaw_pi fun j ↦
    ensemble.mass_hasLaw (W * k + offset + j.val)

/-- Windows from distinct block indices are independent. -/
theorem massWindow_indepFun
    (ensemble : IIDMassPhaseEnsemble Omega) {W offset i k : Nat}
    (hik : i ≠ k) :
    (massWindow ensemble W offset i) ⟂ᵢ[ensemble.probability]
      (massWindow ensemble W offset k) := by
  let S := massWindowIndexSet W offset i
  let T := massWindowIndexSet W offset k
  have hbase :
      (fun omega (n : S) ↦ ensemble.mass n.val omega)
          ⟂ᵢ[ensemble.probability]
        (fun omega (n : T) ↦ ensemble.mass n.val omega) :=
    ensemble.mass_iIndep.indepFun_finset S T
      (massWindowIndexSet_disjoint hik) ensemble.mass_measurable
  have hcomp := hbase.comp
    (measurable_extractMassWindow W offset i)
    (measurable_extractMassWindow W offset k)
  convert hcomp using 1 <;> ext omega j <;>
    rfl

/-- Applying the same measurable local observable preserves independence of
distinct non-overlapping windows. -/
theorem windowObservable_indepFun
    (ensemble : IIDMassPhaseEnsemble Omega) {W offset i k : Nat}
    (f : (Fin W → Real) → Real) (hf : Measurable f)
    (hik : i ≠ k) :
    (windowObservable ensemble W offset f i)
        ⟂ᵢ[ensemble.probability]
      (windowObservable ensemble W offset f k) := by
  exact (massWindow_indepFun ensemble hik).comp hf hf

/-- All windows in a fixed residue class are identically distributed. -/
theorem windowObservable_identDistrib
    (ensemble : IIDMassPhaseEnsemble Omega) (W offset : Nat)
    (f : (Fin W → Real) → Real) (hf : Measurable f) (k : Nat) :
    IdentDistrib (windowObservable ensemble W offset f k)
      (windowObservable ensemble W offset f 0)
      ensemble.probability ensemble.probability := by
  have hwindow :=
    (massWindow_hasLaw ensemble W offset k).identDistrib
      (massWindow_hasLaw ensemble W offset 0)
  have hcomp := hwindow.comp hf
  change IdentDistrib
    (fun omega ↦ f (massWindow ensemble W offset k omega))
    (fun omega ↦ f (massWindow ensemble W offset 0 omega))
    ensemble.probability ensemble.probability
  simpa [Function.comp_def] using hcomp

/-- Strong law for a measurable local observable sampled on one fixed class
of non-overlapping length-`W` windows.  The pointwise support bound is exactly
the finite-product input needed for integrability. -/
theorem fixedOffset_windowObservable_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (W offset : Nat)
    (f : (Fin W → Real) → Real) (hf : Measurable f)
    (C : Real)
    (hbound : ∀ x : Fin W → Real,
      (∀ j, x j ∈ RandomEnsemble.massSupport) → ‖f x‖ ≤ C) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat ↦
          (∑ k ∈ Finset.range n,
            windowObservable ensemble W offset f k omega) / (n : Real))
        atTop
        (𝓝 (∫ omega,
          windowObservable ensemble W offset f 0 omega
            ∂ensemble.probability)) := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  let X : Nat → Omega → Real :=
    fun k ↦ windowObservable ensemble W offset f k
  have hint : Integrable (X 0) ensemble.probability :=
    Integrable.of_bound
      (measurable_windowObservable ensemble W offset f hf 0).aestronglyMeasurable
      C
      (ae_of_all _ fun omega ↦
        hbound (massWindow ensemble W offset 0 omega)
          (massWindow_mem_support ensemble W offset 0 omega))
  have hindep : Pairwise ((· ⟂ᵢ[ensemble.probability] ·) on X) := by
    intro i k hik
    exact windowObservable_indepFun ensemble f hf hik
  have hident : ∀ k, IdentDistrib (X k) (X 0)
      ensemble.probability ensemble.probability := by
    intro k
    exact windowObservable_identDistrib ensemble W offset f hf k
  simpa [X] using strong_law_ae_real X hint hindep hident

/-- There is one full-measure event on which the block strong law holds for
every residue `offset : Fin W`.  This finite-intersection form is the direct
input for recombining residue classes into a sliding-window spatial average. -/
theorem allOffsets_windowObservable_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (W : Nat)
    (f : (Fin W → Real) → Real) (hf : Measurable f)
    (C : Real)
    (hbound : ∀ x : Fin W → Real,
      (∀ j, x j ∈ RandomEnsemble.massSupport) → ‖f x‖ ≤ C) :
    ∀ᵐ omega ∂ensemble.probability, ∀ offset : Fin W,
      Tendsto
        (fun n : Nat ↦
          (∑ k ∈ Finset.range n,
            windowObservable ensemble W offset.val f k omega) / (n : Real))
        atTop
        (𝓝 (∫ omega,
          windowObservable ensemble W offset.val f 0 omega
            ∂ensemble.probability)) := by
  apply ae_all_iff.mpr
  intro offset
  exact fixedOffset_windowObservable_strongLaw_ae ensemble W offset.val
    f hf C hbound

end

end ArchonPhysics.FiniteWindowIIDStrongLaw
