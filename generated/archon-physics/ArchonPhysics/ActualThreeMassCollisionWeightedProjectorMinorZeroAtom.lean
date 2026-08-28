import ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorTail
import ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
import ArchonPhysics.ActualThreeMassWeightedProjectorMinorScaleBound

open scoped Matrix BigOperators ENNReal

namespace ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorZeroAtom

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorBadPeak
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.ActualThreeMassWeightedProjectorMinorDistribution
open ArchonPhysics.ActualThreeMassWeightedProjectorMinorScaleBound
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set

noncomputable section

/-- Exact raw-mass zero locus of one genuine projector minor. -/
def actualThreeMassProjectorMinorZeroSet
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) : Set MassTriple :=
  actualThreeMassProjectorMinorMagnitude
    fixed site₀ site₁ site₂ modes ⁻¹' {0}

theorem measurableSet_actualThreeMassProjectorMinorZeroSet
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) :
    MeasurableSet (actualThreeMassProjectorMinorZeroSet
      fixed site₀ site₁ site₂ modes) :=
  measurableSet_singleton 0 |>.preimage
    (measurable_actualThreeMassProjectorMinorMagnitude
      fixed site₀ site₁ site₂ modes)

/-- The zero atom of the true collision-weighted minor law is exactly the
finite per-site sum of the physical collision source on the modewise actual
minor-zero loci. -/
theorem actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_singleton_zero_eq
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) :
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ ({0} : Set Real) =
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          (iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes))
            (actualThreeMassProjectorMinorZeroSet
              fixed site₀ site₁ site₂ modes) := by
  classical
  unfold actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro modes _hmodes
  rw [Measure.map_apply
    (measurable_actualThreeMassProjectorMinorMagnitude
      fixed site₀ site₁ site₂ modes) (measurableSet_singleton 0)]
  rfl

/-- Since `N > 0`, the actual zero atom vanishes exactly when every modewise
collision-weighted zero-locus term vanishes. -/
theorem actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_singleton_zero_iff
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) :
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ ({0} : Set Real) = 0 ↔
      ∀ modes : OrderedModeTriple N,
        (iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes))
          (actualThreeMassProjectorMinorZeroSet
            fixed site₀ site₁ site₂ modes) = 0 := by
  classical
  rw [actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_singleton_zero_eq]
  constructor
  · intro hzero modes
    have hinv : (N : ENNReal)⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
    have hsum :
        (∑ modes : OrderedModeTriple N,
          (iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes))
            (actualThreeMassProjectorMinorZeroSet
              fixed site₀ site₁ site₂ modes)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hinv
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun _modes _hmodes => bot_le)).mp hsum modes (Finset.mem_univ modes)
  · intro hzero
    simp [hzero]

theorem modewiseProjectorMinorZeroMass_eq_zero_of_not_allDistinct
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) (hdistinct : ¬ AllDistinctModes modes) :
    (iidMassTripleLaw.withDensity
      (actualThreeMassAllDistinctTupleWeight
        fixed site₀ site₁ site₂ modes))
      (actualThreeMassProjectorMinorZeroSet
        fixed site₀ site₁ site₂ modes) = 0 := by
  have hweight :
      actualThreeMassAllDistinctTupleWeight
        fixed site₀ site₁ site₂ modes = fun _triple => 0 := by
    funext triple
    simp [actualThreeMassAllDistinctTupleWeight, hdistinct]
  rw [hweight]
  simp

/-- It is enough to prove the actual zero-locus nullity for statically
all-distinct mode labels; every other term is identically killed by the
physical sector weight. -/
theorem actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_singleton_zero_iff_allDistinct
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) :
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ ({0} : Set Real) = 0 ↔
      ∀ modes : OrderedModeTriple N, AllDistinctModes modes →
        (iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes))
          (actualThreeMassProjectorMinorZeroSet
            fixed site₀ site₁ site₂ modes) = 0 := by
  rw [actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_singleton_zero_iff]
  constructor
  · intro hall modes _hdistinct
    exact hall modes
  · intro hall modes
    by_cases hdistinct : AllDistinctModes modes
    · exact hall modes hdistinct
    · exact modewiseProjectorMinorZeroMass_eq_zero_of_not_allDistinct
        fixed site₀ site₁ site₂ modes hdistinct

/-- Exact polynomial-numerator reduction for the actual zero atom.

This theorem does **not** manufacture the polynomials.  Its model-specific
premise is precisely the missing bridge: for every all-distinct ordered mode
triple, supply a nonzero inverse-mass polynomial whose zero set contains the
actual projector-minor zero locus on the frozen iid support.  The existing
iid polynomial-avoidance theorem then removes that locus, and the finite
mode sum gives the desired zero atom. -/
theorem actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_singleton_zero_of_polynomialNumerators
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (numerator : OrderedModeTriple N → MvPolynomial (Fin 3) Real)
    (hnumerator : ∀ modes, AllDistinctModes modes → numerator modes ≠ 0)
    (hzeroLocus : ∀ modes triple, AllDistinctModes modes →
      triple ∈ iidMassTripleSupport →
      triple ∈ actualThreeMassProjectorMinorZeroSet
        fixed site₀ site₁ site₂ modes →
      MvPolynomial.eval (iidInverseMassTripleCoordinates triple)
        (numerator modes) = 0) :
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ ({0} : Set Real) = 0 := by
  apply
    (actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_singleton_zero_iff_allDistinct
      fixed site₀ site₁ site₂).2
  intro modes hdistinct
  apply (withDensity_absolutelyContinuous iidMassTripleLaw
    (actualThreeMassAllDistinctTupleWeight
      fixed site₀ site₁ site₂ modes))
  apply measure_mono_null (t :=
    {triple |
      MvPolynomial.eval (iidInverseMassTripleCoordinates triple)
        (numerator modes) = 0} ∪ iidMassTripleSupportᶜ)
  · intro triple hminor
    by_cases hsupport : triple ∈ iidMassTripleSupport
    · exact Or.inl (hzeroLocus modes triple hdistinct hsupport hminor)
    · exact Or.inr hsupport
  · apply measure_union_null
    · exact iidMassTripleLaw_zeroSet_eval_inverseCoordinates
        (numerator modes) (hnumerator modes hdistinct)
    · exact (mem_ae_iff.mp iidMassTriple_mem_support_ae)

end

end ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorZeroAtom
