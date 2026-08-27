import Mathlib.Analysis.Calculus.FDeriv.Measurable
import ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
import ArchonPhysics.SimpleSpectrumProjectorContinuity

/-!
# Regularity of the actual three-mass projector minor

The actual dual-cycle projector minor is globally measurable and locally
continuous at every simple-spectrum mass triple.  These facts make its
good-determinant levels legitimate measurable coarea regions.  No nullity
or pointwise nondegeneracy statement is made here.
-/

open scoped Matrix

namespace ArchonPhysics.ActualThreeMassProjectorMinorRegularity

open ArchonPhysics
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.SimpleSpectrumProjectorContinuity
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open Set

noncomputable section

/-- The genuine dual Hermitian matrix is continuous in all three clipped raw
mass coordinates. -/
theorem continuous_actualThreeMassDualHermitian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) :
    Continuous (actualThreeMassDualHermitian fixed site₀ site₁ site₂) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous fun triple : MassTriple =>
    ∑ k, threeMassBondMatrix fixed site₀ site₁ site₂ triple i k *
      threeMassBondMatrix fixed site₀ site₁ site₂ triple j k
  apply continuous_finsetSum Finset.univ
  intro k _hk
  exact (continuous_threeMassBondMatrix_apply
    fixed site₀ site₁ site₂ i k).mul
      (continuous_threeMassBondMatrix_apply
        fixed site₀ site₁ site₂ j k)

/-- Every entry of the totalized actual projector-weight matrix is globally
measurable, including at spectral collisions. -/
theorem measurable_actualThreeMassProjectorWeightMatrix_apply
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (r s : Fin 3) :
    Measurable fun triple : MassTriple =>
      actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes triple r s := by
  let direction : Lattice.Configuration N :=
    actualThreeMassCycleDirection site₀ site₁ site₂ s
  change Measurable fun triple : MassTriple =>
    ∑ i, direction i *
      ∑ j, orderedModeProjector
        (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple)
          (modes r) i j * direction j
  apply Finset.measurable_sum
  intro i _hi
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro j _hj
  exact ((measurable_orderedModeProjector_apply (modes r) i j).comp
    (continuous_actualThreeMassDualHermitian
      fixed site₀ site₁ site₂).measurable).mul measurable_const

/-- The actual projector-minor determinant is a globally measurable scalar.
This is the measurability needed for good/bad determinant restrictions. -/
theorem measurable_actualThreeMassProjectorWeightMatrix_det
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))) :
    Measurable fun triple : MassTriple =>
      (actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes triple).det := by
  simp only [Matrix.det_apply']
  apply Finset.measurable_sum
  intro permutation _hpermutation
  apply measurable_const.mul
  apply Finset.measurable_prod Finset.univ
  intro i _hi
  exact measurable_actualThreeMassProjectorWeightMatrix_apply
    fixed site₀ site₁ site₂ modes (permutation i) i

/-- At a simple physical spectrum, every actual projector-weight entry is
continuous in the three raw masses. -/
theorem continuousAt_actualThreeMassProjectorWeightMatrix_apply
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (r s : Fin 3) :
    ContinuousAt
      (fun nearby : MassTriple =>
        actualThreeMassProjectorWeightMatrix
          fixed site₀ site₁ site₂ modes nearby r s) triple := by
  let sample : MassTriple → HermitianMatrix (Lattice.Site N) :=
    actualThreeMassDualHermitian fixed site₀ site₁ site₂
  let direction : Lattice.Configuration N :=
    actualThreeMassCycleDirection site₀ site₁ site₂ s
  have hsimpleDual : SimpleOrderedSpectrum (sample triple) := by
    simpa [sample] using simple_actualThreeMassDualHermitian_of_simple
      fixed site₀ site₁ site₂ triple hsimple
  change ContinuousAt (fun nearby : MassTriple =>
    ∑ i, direction i *
      ∑ j, orderedModeProjector (sample nearby) (modes r) i j *
        direction j) triple
  apply tendsto_finsetSum Finset.univ
  intro i _hi
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_finsetSum Finset.univ
  intro j _hj
  apply ContinuousAt.mul
  · exact (continuousAt_orderedModeProjector_apply
      (sample triple) hsimpleDual (modes r) i j).comp_of_eq
        (continuous_actualThreeMassDualHermitian
          fixed site₀ site₁ site₂).continuousAt rfl
  · exact continuousAt_const

/-- Consequently the actual projector minor determinant is locally
continuous throughout the simple-spectrum locus. -/
theorem continuousAt_actualThreeMassProjectorWeightMatrix_det
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)) :
    ContinuousAt
      (fun nearby : MassTriple =>
        (actualThreeMassProjectorWeightMatrix
          fixed site₀ site₁ site₂ modes nearby).det) triple := by
  simp only [Matrix.det_apply']
  apply tendsto_finsetSum Finset.univ
  intro permutation _hpermutation
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_finsetProd Finset.univ
  intro i _hi
  exact continuousAt_actualThreeMassProjectorWeightMatrix_apply
    fixed site₀ site₁ site₂ modes hsimple (permutation i) i

/-- The exact actual source on which the projector minor, and hence the
lifted Jacobian, is nonzero.  This definition does not assert that the source
has full iid measure. -/
def actualThreeMassProjectorRegularSource
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))) :
    Set MassTriple :=
  {triple |
    triple ∈ interior iidMassTripleSupport ∧
    SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple) ∧
    (∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) ∧
    (actualThreeMassProjectorWeightMatrix
      fixed site₀ site₁ site₂ modes triple).det ≠ 0}

/-- The projector source is exactly the ordinary actual lifted regularity
conditions, for every interaction-sign choice. -/
theorem mem_actualThreeMassProjectorRegularSource_iff_lifted
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → ModalPhaseMismatch.InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) :
    triple ∈ actualThreeMassProjectorRegularSource
        fixed site₀ site₁ site₂ modes ↔
      triple ∈ interior iidMassTripleSupport ∧
      SimpleOrderedSpectrum
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple) ∧
      (∀ r, 0 < orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
          (modes r)) ∧
      (actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes triple).det ≠ 0 := by
  constructor
  · intro hregular
    refine ⟨hregular.1, hregular.2.1, hregular.2.2.1, ?_⟩
    exact (actualThreeMassLiftedFrequencyJacobian_det_ne_zero_iff_projectorWeight
      fixed h₁₀ h₂₀ h₂₁ sign modes hregular.1 hregular.2.1
        hregular.2.2.1).2 hregular.2.2.2
  · intro hregular
    refine ⟨hregular.1, hregular.2.1, hregular.2.2.1, ?_⟩
    exact (actualThreeMassLiftedFrequencyJacobian_det_ne_zero_iff_projectorWeight
      fixed h₁₀ h₂₀ h₂₁ sign modes hregular.1 hregular.2.1
        hregular.2.2.1).1 hregular.2.2.2

theorem measurableSet_actualThreeMassProjectorRegularSource
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))) :
    MeasurableSet (actualThreeMassProjectorRegularSource
      fixed site₀ site₁ site₂ modes) := by
  have hsimpleOpen : IsOpen
      {triple : MassTriple | SimpleOrderedSpectrum
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)} := by
    rw [isOpen_iff_mem_nhds]
    intro triple hsimple
    exact eventually_simple_threeMassHarmonicHermitian
      fixed site₀ site₁ site₂ triple hsimple
  have hpositive : MeasurableSet
      {triple : MassTriple | ∀ r, 0 < orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
          (modes r)} := by
    rw [show {triple : MassTriple | ∀ r, 0 < orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
          (modes r)} =
      ⋂ r, {triple : MassTriple | 0 < orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
          (modes r)} by ext; simp]
    apply MeasurableSet.iInter
    intro r
    exact measurableSet_Ioi.preimage
      ((continuous_orderedEigenvalue (modes r)).measurable.comp
        (continuous_threeMassHarmonicHermitian
          fixed site₀ site₁ site₂).measurable)
  have hdet : MeasurableSet
      {triple : MassTriple |
        (actualThreeMassProjectorWeightMatrix
          fixed site₀ site₁ site₂ modes triple).det ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage
      (measurable_actualThreeMassProjectorWeightMatrix_det
        fixed site₀ site₁ site₂ modes)
  have hinterior : MeasurableSet (interior iidMassTripleSupport) :=
    isOpen_interior.measurableSet
  unfold actualThreeMassProjectorRegularSource
  exact hinterior.inter
    (hsimpleOpen.measurableSet.inter (hpositive.inter hdet))

/-- Reciprocal-natural levels of the actual projector minor inside its exact
regular source. -/
def actualThreeMassProjectorGoodDetLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (n : Nat) : Set MassTriple :=
  {triple |
    triple ∈ actualThreeMassProjectorRegularSource
      fixed site₀ site₁ site₂ modes ∧
    1 / ((n : Real) + 1) ≤
      |(actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes triple).det|}

theorem measurableSet_actualThreeMassProjectorGoodDetLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (n : Nat) :
    MeasurableSet (actualThreeMassProjectorGoodDetLevel
      fixed site₀ site₁ site₂ modes n) := by
  exact (measurableSet_actualThreeMassProjectorRegularSource
    fixed site₀ site₁ site₂ modes).inter
      (measurableSet_Ici.preimage
        (measurable_actualThreeMassProjectorWeightMatrix_det
          fixed site₀ site₁ site₂ modes).abs)

theorem monotone_actualThreeMassProjectorGoodDetLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))) :
    Monotone (actualThreeMassProjectorGoodDetLevel
      fixed site₀ site₁ site₂ modes) := by
  intro n m hnm triple htriple
  refine ⟨htriple.1, ?_⟩
  exact (one_div_le_one_div_of_le (by positivity) (by
    exact_mod_cast Nat.add_le_add_right hnm 1)).trans htriple.2

/-- The monotone good levels cover every regular point.  This is only a
pointwise coverage theorem; obtaining a volume-uniform weighted bad-mass
modulus is the remaining probabilistic/algebraic task. -/
theorem actualThreeMassProjectorRegularSource_subset_iUnion_goodDetLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))) :
    actualThreeMassProjectorRegularSource fixed site₀ site₁ site₂ modes ⊆
      ⋃ n, actualThreeMassProjectorGoodDetLevel
        fixed site₀ site₁ site₂ modes n := by
  intro triple hregular
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt
    (abs_pos.mpr hregular.2.2.2)
  exact mem_iUnion.mpr ⟨n, hregular, hn.le⟩

/-- The genuine lifted Jacobian determinant is globally measurable because
it is the determinant of the Fréchet derivative of the continuous actual
chart. -/
theorem measurable_actualThreeMassLiftedFrequencyJacobian_det
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → ModalPhaseMismatch.InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))) :
    Measurable fun triple : MassTriple =>
      (actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes triple).det := by
  change Measurable fun triple : MassTriple =>
    (fderiv Real
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes) triple).det
  exact ContinuousLinearMap.continuous_det.measurable.comp
    (measurable_fderiv Real
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes))

/-- Sign-dependent reciprocal-natural levels of the actual lifted
Jacobian.  Unlike the projector levels, these are ready to supply the
`detLower` premise of the quantitative coarea theorem. -/
def actualThreeMassLiftedGoodDetLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → ModalPhaseMismatch.InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (n : Nat) : Set MassTriple :=
  {triple |
    triple ∈ actualThreeMassProjectorRegularSource
      fixed site₀ site₁ site₂ modes ∧
    1 / ((n : Real) + 1) ≤
      |(actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes triple).det|}

theorem measurableSet_actualThreeMassLiftedGoodDetLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → ModalPhaseMismatch.InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (n : Nat) :
    MeasurableSet (actualThreeMassLiftedGoodDetLevel
      fixed site₀ site₁ site₂ sign modes n) := by
  exact (measurableSet_actualThreeMassProjectorRegularSource
    fixed site₀ site₁ site₂ modes).inter
      (measurableSet_Ici.preimage
        (measurable_actualThreeMassLiftedFrequencyJacobian_det
          fixed site₀ site₁ site₂ sign modes).abs)

theorem monotone_actualThreeMassLiftedGoodDetLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → ModalPhaseMismatch.InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))) :
    Monotone (actualThreeMassLiftedGoodDetLevel
      fixed site₀ site₁ site₂ sign modes) := by
  intro n m hnm triple htriple
  refine ⟨htriple.1, ?_⟩
  exact (one_div_le_one_div_of_le (by positivity) (by
    exact_mod_cast Nat.add_le_add_right hnm 1)).trans htriple.2

/-- For each fixed chart, the actual lifted levels cover its exact regular
source.  This does not provide a volume-uniform choice of level. -/
theorem actualThreeMassProjectorRegularSource_subset_iUnion_liftedGoodDetLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → ModalPhaseMismatch.InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))) :
    actualThreeMassProjectorRegularSource fixed site₀ site₁ site₂ modes ⊆
      ⋃ n, actualThreeMassLiftedGoodDetLevel
        fixed site₀ site₁ site₂ sign modes n := by
  intro triple hregular
  have hdet :
      (actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes triple).det ≠ 0 :=
    (actualThreeMassLiftedFrequencyJacobian_det_ne_zero_iff_projectorWeight
      fixed h₁₀ h₂₀ h₂₁ sign modes hregular.1 hregular.2.1
        hregular.2.2.1).2 hregular.2.2.2
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hdet)
  exact mem_iUnion.mpr ⟨n, hregular, hn.le⟩

end

end ArchonPhysics.ActualThreeMassProjectorMinorRegularity
