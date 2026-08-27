import ArchonPhysics.ActualThreeMassLiftedJacobianDeterminantIdentity
import ArchonPhysics.ActualThreeMassProjectorMinorRegularity

/-!
# Continuity and compact lower bounds for the actual lifted Jacobian

The exact Hellmann--Feynman determinant identity makes the true lifted
Jacobian determinant locally continuous throughout the interior
simple-positive locus.  Consequently the exact projector-regular source is
open, and every compact subset of it has a strictly positive actual
Jacobian threshold.
-/

namespace ArchonPhysics.ActualThreeMassLiftedJacobianContinuity

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedJacobianDeterminantIdentity
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorMinorRegularity
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter Set
open scoped Matrix

noncomputable section

/-- The explicit scaled-projector frequency Jacobian is locally continuous
at every interior simple-positive point. -/
theorem continuousAt_actualThreeMassFrequencyProjectorJacobianMatrix
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) :
    ContinuousAt
      (fun nearby => actualThreeMassFrequencyProjectorJacobianMatrix
        fixed site₀ site₁ site₂ modes nearby) triple := by
  have hrow : ∀ r, ContinuousAt
      (fun nearby => actualThreeMassFrequencyRowScale
        fixed site₀ site₁ site₂ modes nearby r) triple := by
    intro r
    unfold actualThreeMassFrequencyRowScale
    have hfrequency : ContinuousAt
        (fun nearby => orderedModeFrequency
          (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
            (modes r)) triple :=
      ((continuous_orderedModeFrequency (modes r)).comp
        (continuous_threeMassHarmonicHermitian
          fixed site₀ site₁ site₂)).continuousAt
    exact (continuousAt_const.mul hfrequency).inv₀
      (mul_ne_zero (by norm_num)
        (Real.sqrt_ne_zero'.2 (hpositive r)))
  have hcolumn : ∀ s, ContinuousAt
      (fun nearby => actualThreeMassRawMassColumnScale nearby s) triple := by
    intro s
    have hcoordinate : Continuous
        (fun nearby : MassTriple => actualThreeMassRawCoordinate nearby s) := by
      fin_cases s
      · change Continuous (fun nearby : MassTriple => nearby.1.1)
        fun_prop
      · change Continuous (fun nearby : MassTriple => nearby.1.2)
        fun_prop
      · change Continuous (fun nearby : MassTriple => nearby.2)
        fun_prop
    unfold actualThreeMassRawMassColumnScale
    exact ((hcoordinate.continuousAt.pow 2).inv₀
      (pow_ne_zero 2
        (actualThreeMassRawCoordinate_ne_zero htriple s))).neg
  apply continuousAt_pi'
  intro r
  apply continuousAt_pi'
  intro s
  change ContinuousAt (fun nearby =>
    actualThreeMassFrequencyRowScale
        fixed site₀ site₁ site₂ modes nearby r *
      actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes nearby r s *
      actualThreeMassRawMassColumnScale nearby s) triple
  exact ((hrow r).mul
    (continuousAt_actualThreeMassProjectorWeightMatrix_apply
      fixed site₀ site₁ site₂ modes hsimple r s)).mul (hcolumn s)

theorem continuousAt_actualThreeMassFrequencyProjectorJacobianMatrix_det
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) :
    ContinuousAt
      (fun nearby => (actualThreeMassFrequencyProjectorJacobianMatrix
        fixed site₀ site₁ site₂ modes nearby).det) triple := by
  exact continuous_id.matrix_det.continuousAt.comp_of_eq
    (continuousAt_actualThreeMassFrequencyProjectorJacobianMatrix
      fixed site₀ site₁ site₂ modes htriple hsimple hpositive) rfl

/-- The determinant of the genuine `fderiv`-defined lifted chart is locally
continuous on its actual differentiability locus. -/
theorem continuousAt_actualThreeMassLiftedFrequencyJacobian_det
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) :
    ContinuousAt
      (fun nearby => (actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes nearby).det) triple := by
  have hrhs : ContinuousAt (fun nearby =>
      (sign 0).coefficient *
        (actualThreeMassFrequencyProjectorJacobianMatrix
          fixed site₀ site₁ site₂ modes nearby).det) triple :=
    continuousAt_const.mul
      (continuousAt_actualThreeMassFrequencyProjectorJacobianMatrix_det
        fixed site₀ site₁ site₂ modes htriple hsimple hpositive)
  have hpositiveEventually : ∀ᶠ nearby in nhds triple,
      ∀ r, 0 < orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
          (modes r) := by
    rw [eventually_all]
    intro r
    exact (((continuous_orderedEigenvalue (modes r)).comp
      (continuous_threeMassHarmonicHermitian
        fixed site₀ site₁ site₂)).continuousAt.eventually
          (isOpen_Ioi.mem_nhds (hpositive r)))
  have heq :
      (fun nearby => (actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes nearby).det) =ᶠ[nhds triple]
      (fun nearby => (sign 0).coefficient *
        (actualThreeMassFrequencyProjectorJacobianMatrix
          fixed site₀ site₁ site₂ modes nearby).det) := by
    filter_upwards [isOpen_interior.mem_nhds htriple,
      eventually_simple_threeMassHarmonicHermitian
        fixed site₀ site₁ site₂ triple hsimple,
      hpositiveEventually] with nearby hnearby hsimpleNearby hpositiveNearby
    exact actualThreeMassLiftedFrequencyJacobian_det_eq_frequencyProjector
      fixed h₁₀ h₂₀ h₂₁ sign modes hnearby hsimpleNearby hpositiveNearby
  exact hrhs.congr_of_eventuallyEq heq

/-- The exact actual projector-regular source is open. -/
theorem isOpen_actualThreeMassProjectorRegularSource
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N))) :
    IsOpen (actualThreeMassProjectorRegularSource
      fixed site₀ site₁ site₂ modes) := by
  rw [isOpen_iff_mem_nhds]
  intro triple hregular
  have hpositiveEventually : ∀ᶠ nearby in nhds triple,
      ∀ r, 0 < orderedEigenvalue
        (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
          (modes r) := by
    rw [eventually_all]
    intro r
    exact (((continuous_orderedEigenvalue (modes r)).comp
      (continuous_threeMassHarmonicHermitian
        fixed site₀ site₁ site₂)).continuousAt.eventually
          (isOpen_Ioi.mem_nhds (hregular.2.2.1 r)))
  have hdetEventually : ∀ᶠ nearby in nhds triple,
      (actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes nearby).det ≠ 0 :=
    ((continuousAt_actualThreeMassProjectorWeightMatrix_det
      fixed site₀ site₁ site₂ modes hregular.2.1).ne_iff_eventually_ne
        continuousAt_const).1 hregular.2.2.2
  filter_upwards [isOpen_interior.mem_nhds hregular.1,
    eventually_simple_threeMassHarmonicHermitian
      fixed site₀ site₁ site₂ triple hregular.2.1,
    hpositiveEventually, hdetEventually] with
      nearby hnearby hsimpleNearby hpositiveNearby hdetNearby
  exact ⟨hnearby, hsimpleNearby, hpositiveNearby, hdetNearby⟩

/-- Every compact subset of the actual regular source has a strictly
positive lower bound for the true lifted Jacobian determinant. -/
theorem exists_positive_actualThreeMassLiftedJacobian_detLower_on_compact
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (K : Set MassTriple) (hK : IsCompact K)
    (hKregular : K ⊆ actualThreeMassProjectorRegularSource
      fixed site₀ site₁ site₂ modes) :
    ∃ detLower : Real, 0 < detLower ∧ ∀ point ∈ K,
      detLower ≤
        |(actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point).det| := by
  let jacobianDet : MassTriple → Real := fun point =>
    (actualThreeMassLiftedFrequencyJacobian
      fixed site₀ site₁ site₂ sign modes point).det
  have hcontinuous : ContinuousOn (fun point => |jacobianDet point|) K := by
    intro point hpoint
    have hregular := hKregular hpoint
    exact (continuousAt_actualThreeMassLiftedFrequencyJacobian_det
      fixed h₁₀ h₂₀ h₂₁ sign modes hregular.1 hregular.2.1
        hregular.2.2.1).abs.continuousWithinAt
  have hnonzero : ∀ point ∈ K, jacobianDet point ≠ 0 := by
    intro point hpoint
    exact ((mem_actualThreeMassProjectorRegularSource_iff_lifted
      fixed h₁₀ h₂₀ h₂₁ sign modes point).1
        (hKregular hpoint)).2.2.2
  by_cases hKnonempty : K.Nonempty
  · obtain ⟨point, hpoint, hminimum⟩ :=
      hK.exists_isMinOn hKnonempty hcontinuous
    refine ⟨|jacobianDet point|, abs_pos.mpr (hnonzero point hpoint), ?_⟩
    intro nearby hnearby
    exact hminimum hnearby
  · refine ⟨1, one_pos, ?_⟩
    intro point hpoint
    exact (hKnonempty ⟨point, hpoint⟩).elim

end

end ArchonPhysics.ActualThreeMassLiftedJacobianContinuity
