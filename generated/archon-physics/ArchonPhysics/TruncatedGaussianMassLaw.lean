import ArchonPhysics.RandomEnsemble

/-!
# Positive Gaussian random masses on the frozen compact support

An ordinary real Gaussian assigns positive probability to negative masses.
For a Hamiltonian mass matrix this is not an admissible law.  This module
therefore conditions a nondegenerate real Gaussian on the already frozen
physical mass interval `[4 / 5, 6 / 5]`.

The conditioned law is a probability measure, is supported on that interval,
and has exactly the same null sets there as restricted Lebesgue measure.  In
particular every open patch meeting the interior of the mass interval has
positive probability.

This file is probability infrastructure only.  It makes no localization,
kinetic-limit, thermalization-time, or long-time-equilibrium assertion.
-/

namespace ArchonPhysics.TruncatedGaussianMassLaw

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

open RandomEnsemble

/-- Parameters of a nondegenerate real Gaussian before conditioning. -/
structure Parameters where
  /-- Mean of the unconditioned Gaussian. -/
  mean : Real
  /-- Variance of the unconditioned Gaussian. -/
  variance : NNReal
  /-- Nondegeneracy is essential for equivalence with Lebesgue measure. -/
  variance_ne_zero : variance ≠ 0

/-- A nondegenerate Gaussian conditioned to the positive compact mass box. -/
def coordinateLaw (parameters : Parameters) : Measure Real :=
  ProbabilityTheory.cond
    (ProbabilityTheory.gaussianReal parameters.mean parameters.variance)
    massSupport

theorem volume_massSupport_pos : 0 < volume massSupport := by
  simp [massSupport, massLower, massUpper, Real.volume_Icc]
  norm_num

/-- Every nondegenerate Gaussian gives the frozen mass interval positive mass. -/
theorem gaussianReal_massSupport_pos (parameters : Parameters) :
    0 < ProbabilityTheory.gaussianReal parameters.mean parameters.variance
      massSupport :=
  (ProbabilityTheory.gaussianReal_absolutelyContinuous'
    parameters.mean parameters.variance_ne_zero).pos_mono volume_massSupport_pos

noncomputable instance coordinateLaw.instIsProbabilityMeasure
    (parameters : Parameters) : IsProbabilityMeasure (coordinateLaw parameters) := by
  unfold coordinateLaw
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (gaussianReal_massSupport_pos parameters).ne'
    (measure_ne_top _ _)

/-- The conditioned law is concentrated on the frozen positive interval. -/
theorem mem_massSupport_ae (parameters : Parameters) :
    ∀ᵐ mass ∂coordinateLaw parameters, mass ∈ massSupport := by
  change ∀ᵐ mass ∂(ProbabilityTheory.gaussianReal parameters.mean
    parameters.variance)[|massSupport], mass ∈ massSupport
  exact ProbabilityTheory.ae_cond_mem
    (show MeasurableSet massSupport from measurableSet_Icc)

/-- The truncated Gaussian has no null sets beyond restricted Lebesgue-null
sets inside the frozen support. -/
theorem coordinateLaw_absolutelyContinuous_volume_restrict
    (parameters : Parameters) :
    coordinateLaw parameters ≪ volume.restrict massSupport := by
  unfold coordinateLaw ProbabilityTheory.cond
  exact Measure.smul_absolutelyContinuous.trans
    ((ProbabilityTheory.gaussianReal_absolutelyContinuous
      parameters.mean parameters.variance_ne_zero).restrict massSupport)

/-- Restricted Lebesgue measure has no null sets beyond truncated-Gaussian
null sets.  Together with the previous theorem this is mutual absolute
continuity on the physical mass box. -/
theorem volume_restrict_absolutelyContinuous_coordinateLaw
    (parameters : Parameters) :
    volume.restrict massSupport ≪ coordinateLaw parameters := by
  unfold coordinateLaw ProbabilityTheory.cond
  exact ((ProbabilityTheory.gaussianReal_absolutelyContinuous'
    parameters.mean parameters.variance_ne_zero).restrict massSupport).smul_right
      (ENNReal.inv_ne_zero.mpr (measure_ne_top
        (ProbabilityTheory.gaussianReal parameters.mean parameters.variance)
        massSupport))

theorem coordinateLaw_null_iff_volume_restrict
    (parameters : Parameters) (s : Set Real) :
    coordinateLaw parameters s = 0 ↔ volume.restrict massSupport s = 0 := by
  constructor
  · intro hs
    exact (volume_restrict_absolutelyContinuous_coordinateLaw parameters) hs
  · intro hs
    exact (coordinateLaw_absolutelyContinuous_volume_restrict parameters) hs

/-- Any open neighbourhood of an interior admissible mass has positive
truncated-Gaussian probability. -/
theorem coordinateLaw_pos_of_isOpen_of_mem_interior
    (parameters : Parameters) {patch : Set Real} (hpatch : IsOpen patch)
    {x : Real} (hx : x ∈ patch) (hxInterior : x ∈ Ioo massLower massUpper) :
    0 < coordinateLaw parameters patch := by
  let interiorPatch : Set Real := patch ∩ Ioo massLower massUpper
  have hopen : IsOpen interiorPatch := hpatch.inter isOpen_Ioo
  have hxPatch : x ∈ interiorPatch := ⟨hx, hxInterior⟩
  have hsubsetSupport : interiorPatch ⊆ massSupport := by
    intro y hy
    exact ⟨hy.2.1.le, hy.2.2.le⟩
  have hvolume : 0 < volume interiorPatch :=
    hopen.measure_pos volume ⟨x, hxPatch⟩
  have hrestricted : 0 < volume.restrict massSupport interiorPatch := by
    rw [Measure.restrict_apply hopen.measurableSet]
    simpa [inter_eq_left.mpr hsubsetSupport] using hvolume
  have hlaw : 0 < coordinateLaw parameters interiorPatch :=
    (volume_restrict_absolutelyContinuous_coordinateLaw parameters).pos_mono hrestricted
  exact hlaw.trans_le (measure_mono inter_subset_left)

/-! ## Finite iid laws and positive open patches -/

/-- Product law of `N` independent truncated-Gaussian masses. -/
def finiteLaw (parameters : Parameters) (N : Nat) : Measure (Fin N → Real) :=
  Measure.pi (fun _ : Fin N ↦ coordinateLaw parameters)

noncomputable instance finiteLaw.instIsProbabilityMeasure
    (parameters : Parameters) (N : Nat) :
    IsProbabilityMeasure (finiteLaw parameters N) := by
  unfold finiteLaw
  infer_instance

/-- Every open neighbourhood of an interior point of the finite mass cube has
positive iid truncated-Gaussian probability. -/
theorem finiteLaw_pos_of_isOpen_of_mem_interior
    (parameters : Parameters) {N : Nat} {patch : Set (Fin N → Real)}
    (hpatch : IsOpen patch) (x : Fin N → Real) (hx : x ∈ patch)
    (hxInterior : ∀ i, x i ∈ Ioo massLower massUpper) :
    0 < finiteLaw parameters N patch := by
  obtain ⟨coordinatePatch, hcoordinatePatch, hsubset⟩ :=
    (isOpen_pi_iff'.mp hpatch) x hx
  let interiorCoordinatePatch : Fin N → Set Real := fun i ↦
    coordinatePatch i ∩ Ioo massLower massUpper
  have hopen (i : Fin N) : IsOpen (interiorCoordinatePatch i) :=
    (hcoordinatePatch i).1.inter isOpen_Ioo
  have hxCoordinate (i : Fin N) : x i ∈ interiorCoordinatePatch i :=
    ⟨(hcoordinatePatch i).2, hxInterior i⟩
  have hrectangleSubset :
      Set.univ.pi interiorCoordinatePatch ⊆ patch := by
    apply hsubset.trans'
    intro y hy i _hi
    exact (hy i (Set.mem_univ i)).1
  have hcoordinatePositive (i : Fin N) :
      0 < coordinateLaw parameters (interiorCoordinatePatch i) :=
    coordinateLaw_pos_of_isOpen_of_mem_interior parameters (hopen i)
      (hxCoordinate i) (hxInterior i)
  have hrectanglePositive :
      0 < finiteLaw parameters N (Set.univ.pi interiorCoordinatePatch) := by
    rw [finiteLaw, Measure.pi_pi]
    exact pos_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun i _hi ↦ (hcoordinatePositive i).ne')
  exact hrectanglePositive.trans_le (measure_mono hrectangleSubset)

end

end ArchonPhysics.TruncatedGaussianMassLaw
