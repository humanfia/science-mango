import ArchonPhysics.IIDMassTripleMarginal

/-!
# Splitting three selected iid masses from a finite frozen environment

For any finite set of coordinates disjoint from three selected sites, the
selected mass triple is independent of the remaining mass vector.  Their
joint law is the product of the explicit mass-triple law and the finite iid
environment law.  This is the finite-volume Fubini/resampling identity needed
to apply an actual three-mass spectral chart with the environment frozen.
-/

namespace ArchonPhysics.IIDMassTripleFiniteEnvironment

open ArchonPhysics
open ArchonPhysics.IIDMassTripleMarginal
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory ProbabilityTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A finite vector of physical mass coordinates indexed by a finite set. -/
abbrev FiniteMassVector (indices : Finset Nat) :=
  (index : indices) → Real

/-- The finite product law of a frozen mass environment. -/
def iidFiniteMassVectorLaw (indices : Finset Nat) :
    Measure (FiniteMassVector indices) :=
  Measure.pi (fun _index : indices => massCoordinateLaw)

/-- The selected finite mass vector in an iid ensemble. -/
def ensembleFiniteMassVector
    (ensemble : IIDMassPhaseEnsemble Omega)
    (indices : Finset Nat) (omega : Omega) :
    FiniteMassVector indices :=
  fun index => ensemble.mass index.1 omega

theorem measurable_ensembleFiniteMassVector
    (ensemble : IIDMassPhaseEnsemble Omega)
    (indices : Finset Nat) :
    Measurable (ensembleFiniteMassVector ensemble indices) := by
  unfold ensembleFiniteMassVector
  exact measurable_pi_lambda _ fun index =>
    ensemble.mass_measurable index.1

/-- Every finite vector of distinct indexed coordinates has its finite
product law. -/
theorem ensembleFiniteMassVector_hasLaw
    (ensemble : IIDMassPhaseEnsemble Omega)
    (indices : Finset Nat) :
    HasLaw (ensembleFiniteMassVector ensemble indices)
      (iidFiniteMassVectorLaw indices) ensemble.probability := by
  have hindependent :
      iIndepFun (fun index : indices => ensemble.mass index.1)
        ensemble.probability :=
    ensemble.mass_iIndep.precomp Subtype.val_injective
  unfold ensembleFiniteMassVector iidFiniteMassVectorLaw
  exact hindependent.hasLaw_pi fun index =>
    ensemble.mass_hasLaw index.1

/-- The finite set containing the three selected coordinates. -/
def selectedMassIndices (i j k : Nat) : Finset Nat :=
  {i, j, k}

/-- Read the nested mass triple from the vector on the selected finite set. -/
def selectedVectorToMassTriple
    (i j k : Nat)
    (values : FiniteMassVector (selectedMassIndices i j k)) :
    MassTriple :=
  ((values ⟨i, by simp [selectedMassIndices]⟩,
    values ⟨j, by simp [selectedMassIndices]⟩),
    values ⟨k, by simp [selectedMassIndices]⟩)

theorem measurable_selectedVectorToMassTriple
    (i j k : Nat) :
    Measurable (selectedVectorToMassTriple i j k) := by
  unfold selectedVectorToMassTriple
  exact ((measurable_pi_apply
    (⟨i, by simp [selectedMassIndices]⟩ :
      selectedMassIndices i j k)).prodMk
      (measurable_pi_apply
        (⟨j, by simp [selectedMassIndices]⟩ :
          selectedMassIndices i j k))).prodMk
          (measurable_pi_apply
            (⟨k, by simp [selectedMassIndices]⟩ :
              selectedMassIndices i j k))

@[simp]
theorem selectedVectorToMassTriple_ensembleFiniteMassVector
    (ensemble : IIDMassPhaseEnsemble Omega)
    (i j k : Nat) (omega : Omega) :
    selectedVectorToMassTriple i j k
        (ensembleFiniteMassVector ensemble (selectedMassIndices i j k) omega) =
      ensembleMassTriple ensemble i j k omega := by
  rfl

/-- The selected triple is independent of every disjoint finite frozen mass
environment. -/
theorem ensembleMassTriple_indep_finiteEnvironment
    (ensemble : IIDMassPhaseEnsemble Omega)
    (i j k : Nat) (rest : Finset Nat)
    (hi : i ∉ rest) (hj : j ∉ rest) (hk : k ∉ rest) :
    IndepFun
      (ensembleMassTriple ensemble i j k)
      (ensembleFiniteMassVector ensemble rest)
      ensemble.probability := by
  have hdisjoint : Disjoint (selectedMassIndices i j k) rest := by
    rw [Finset.disjoint_left]
    intro index hselected hrest
    simp only [selectedMassIndices, Finset.mem_insert,
      Finset.mem_singleton] at hselected
    rcases hselected with hindex | hindex | hindex
    · exact hi (hindex ▸ hrest)
    · exact hj (hindex ▸ hrest)
    · exact hk (hindex ▸ hrest)
  have hgroups :=
    ensemble.mass_iIndep.indepFun_finset
      (selectedMassIndices i j k) rest hdisjoint ensemble.mass_measurable
  have hextract : Measurable
      (fun values : (index : selectedMassIndices i j k) → Real =>
        ((values ⟨i, by simp [selectedMassIndices]⟩,
          values ⟨j, by simp [selectedMassIndices]⟩),
          values ⟨k, by simp [selectedMassIndices]⟩)) := by
    exact ((measurable_pi_apply
      (⟨i, by simp [selectedMassIndices]⟩ :
        selectedMassIndices i j k)).prodMk
        (measurable_pi_apply
          (⟨j, by simp [selectedMassIndices]⟩ :
            selectedMassIndices i j k))).prodMk
              (measurable_pi_apply
                (⟨k, by simp [selectedMassIndices]⟩ :
                  selectedMassIndices i j k))
  have hcomposed := hgroups.comp hextract measurable_id
  change IndepFun
    (fun omega => ((ensemble.mass i omega, ensemble.mass j omega),
      ensemble.mass k omega))
    (fun omega (index : rest) => ensemble.mass index.1 omega)
    ensemble.probability
  apply hcomposed.congr
  · exact Filter.Eventually.of_forall fun omega => rfl
  · exact Filter.Eventually.of_forall fun omega => rfl

/-- Exact product law of the selected mass triple and every disjoint finite
frozen environment. -/
theorem ensembleMassTriple_prod_finiteEnvironment_hasLaw
    (ensemble : IIDMassPhaseEnsemble Omega)
    {i j k : Nat} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rest : Finset Nat)
    (hi : i ∉ rest) (hj : j ∉ rest) (hk : k ∉ rest) :
    HasLaw
      (fun omega =>
        (ensembleMassTriple ensemble i j k omega,
          ensembleFiniteMassVector ensemble rest omega))
      (iidMassTripleLaw.prod (iidFiniteMassVectorLaw rest))
      ensemble.probability := by
  let _ : IsFiniteMeasure ensemble.probability :=
    ⟨by rw [ensemble.probability_univ]; norm_num⟩
  exact
    (ensembleMassTriple_indep_finiteEnvironment
      ensemble i j k rest hi hj hk).hasLaw_prod
        (ensembleMassTriple_hasLaw ensemble hij hik hjk)
        (ensembleFiniteMassVector_hasLaw ensemble rest)

/-- Fubini/resampling identity for every nonnegative measurable observable
of the selected triple and finite frozen environment. -/
theorem lintegral_massTriple_finiteEnvironment_eq_prod
    (ensemble : IIDMassPhaseEnsemble Omega)
    {i j k : Nat} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rest : Finset Nat)
    (hi : i ∉ rest) (hj : j ∉ rest) (hk : k ∉ rest)
    {observable :
      MassTriple × FiniteMassVector rest → ENNReal}
    (hmeasurable : AEMeasurable observable
      (iidMassTripleLaw.prod (iidFiniteMassVectorLaw rest))) :
    ∫⁻ omega,
        observable
          (ensembleMassTriple ensemble i j k omega,
            ensembleFiniteMassVector ensemble rest omega)
        ∂ensemble.probability =
      ∫⁻ state, observable state
        ∂(iidMassTripleLaw.prod (iidFiniteMassVectorLaw rest)) := by
  exact
    (ensembleMassTriple_prod_finiteEnvironment_hasLaw
      ensemble hij hik hjk rest hi hj hk).lintegral_comp hmeasurable

end

end ArchonPhysics.IIDMassTripleFiniteEnvironment
