import ArchonPhysics.SeparatedSpectralClusterProjector

/-!
# Continuous and measurable spectral-band energy observables

The upper band state is obtained by applying the fixed-threshold functional-
calculus matrix to a probe/state vector.  The lower band is its complementary
component.  Their coordinate energies are squared Euclidean norms, hence are
continuous, measurable, and nonnegative without any gap assumption.

When the matrix spectrum is separated by the fixed thresholds, the upper
cluster matrix is Hermitian and idempotent.  The two components are then
orthogonal and their energies add exactly to the total coordinate norm
squared.  No eigenbasis is selected, and internal degeneracies are allowed.
-/

open scoped Matrix

namespace ArchonPhysics.SpectralBandEnergyObservable

open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.SeparatedSpectralClusterProjector

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate squared norm. -/
def coordinateEnergy (x : ι → Real) : Real := x ⬝ᵥ x

omit [DecidableEq ι] in
/-- Coordinate energy is continuous. -/
theorem continuous_coordinateEnergy :
    Continuous (coordinateEnergy (ι := ι)) := by
  unfold coordinateEnergy
  fun_prop

omit [DecidableEq ι] in
/-- Coordinate energy is nonnegative. -/
theorem coordinateEnergy_nonneg (x : ι → Real) :
    0 ≤ coordinateEnergy x := by
  simpa [coordinateEnergy] using dotProduct_star_self_nonneg x

/-- Upper spectral-band component of a probe/state. -/
def upperProjectedState (a b : Real) (A : HermitianMatrix ι)
    (x : ι → Real) : ι → Real :=
  upperClusterProjector a b A *ᵥ x

/-- Complementary lower spectral-band component.  This definition avoids any
ambiguity between the identity matrix and pointwise function `1`. -/
def lowerProjectedState (a b : Real) (A : HermitianMatrix ι)
    (x : ι → Real) : ι → Real :=
  x - upperProjectedState a b A x

/-- Joint continuity of the upper projected state in `(A, x)`. -/
theorem continuous_upperProjectedState (a b : Real) :
    Continuous fun p : HermitianMatrix ι × (ι → Real) =>
      upperProjectedState a b p.1 p.2 := by
  unfold upperProjectedState
  exact ((continuous_upperClusterProjector (ι := ι) a b).comp continuous_fst).matrix_mulVec
    continuous_snd

/-- Joint continuity of the complementary projected state. -/
theorem continuous_lowerProjectedState (a b : Real) :
    Continuous fun p : HermitianMatrix ι × (ι → Real) =>
      lowerProjectedState a b p.1 p.2 := by
  unfold lowerProjectedState
  exact continuous_snd.sub (continuous_upperProjectedState a b)

/-- The lower component is exactly `(I - P)x`. -/
theorem lowerProjectedState_eq_one_sub_mulVec
    (a b : Real) (A : HermitianMatrix ι) (x : ι → Real) :
    lowerProjectedState a b A x =
      ((1 : Matrix ι ι Real) - upperClusterProjector a b A) *ᵥ x := by
  unfold lowerProjectedState upperProjectedState
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

/-- The two components sum to the original state, without a gap premise. -/
theorem upperProjectedState_add_lowerProjectedState
    (a b : Real) (A : HermitianMatrix ι) (x : ι → Real) :
    upperProjectedState a b A x + lowerProjectedState a b A x = x := by
  unfold lowerProjectedState
  abel

/-- Upper-band energy observable. -/
def upperBandEnergy (a b : Real) (A : HermitianMatrix ι)
    (x : ι → Real) : Real :=
  coordinateEnergy (upperProjectedState a b A x)

/-- Complementary lower-band energy observable. -/
def lowerBandEnergy (a b : Real) (A : HermitianMatrix ι)
    (x : ι → Real) : Real :=
  coordinateEnergy (lowerProjectedState a b A x)

/-- Joint continuity of upper-band energy in `(A, x)`. -/
theorem continuous_upperBandEnergy (a b : Real) :
    Continuous fun p : HermitianMatrix ι × (ι → Real) =>
      upperBandEnergy a b p.1 p.2 := by
  exact continuous_coordinateEnergy.comp (continuous_upperProjectedState a b)

/-- Joint continuity of lower-band energy in `(A, x)`. -/
theorem continuous_lowerBandEnergy (a b : Real) :
    Continuous fun p : HermitianMatrix ι × (ι → Real) =>
      lowerBandEnergy a b p.1 p.2 := by
  exact continuous_coordinateEnergy.comp (continuous_lowerProjectedState a b)

/-- Coordinatewise measurability of the upper projected state. -/
theorem measurable_upperProjectedState_apply
    {Omega : Type*} [MeasurableSpace Omega]
    (a b : Real) (sample : Omega → HermitianMatrix ι)
    (state : Omega → ι → Real) (hsample : Measurable sample)
    (hstate : Measurable state) (i : ι) :
    Measurable fun omega => upperProjectedState a b (sample omega) (state omega) i := by
  unfold upperProjectedState Matrix.mulVec dotProduct
  apply Finset.measurable_sum
  intro j _hj
  exact (measurable_upperClusterProjector_apply a b sample hsample i j).mul
    hstate.eval

/-- Coordinatewise measurability of the complementary projected state. -/
theorem measurable_lowerProjectedState_apply
    {Omega : Type*} [MeasurableSpace Omega]
    (a b : Real) (sample : Omega → HermitianMatrix ι)
    (state : Omega → ι → Real) (hsample : Measurable sample)
    (hstate : Measurable state) (i : ι) :
    Measurable fun omega => lowerProjectedState a b (sample omega) (state omega) i := by
  unfold lowerProjectedState
  exact hstate.eval.sub
    (measurable_upperProjectedState_apply a b sample state hsample hstate i)

/-- A measurable random Hermitian sample and random state give a measurable
upper-band energy. -/
theorem measurable_upperBandEnergy
    {Omega : Type*} [MeasurableSpace Omega]
    (a b : Real) (sample : Omega → HermitianMatrix ι)
    (state : Omega → ι → Real) (hsample : Measurable sample)
    (hstate : Measurable state) :
    Measurable fun omega => upperBandEnergy a b (sample omega) (state omega) := by
  unfold upperBandEnergy coordinateEnergy dotProduct
  apply Finset.measurable_sum
  intro i _hi
  exact (measurable_upperProjectedState_apply a b sample state hsample hstate i).mul
    (measurable_upperProjectedState_apply a b sample state hsample hstate i)

/-- Measurability of complementary lower-band energy. -/
theorem measurable_lowerBandEnergy
    {Omega : Type*} [MeasurableSpace Omega]
    (a b : Real) (sample : Omega → HermitianMatrix ι)
    (state : Omega → ι → Real) (hsample : Measurable sample)
    (hstate : Measurable state) :
    Measurable fun omega => lowerBandEnergy a b (sample omega) (state omega) := by
  unfold lowerBandEnergy coordinateEnergy dotProduct
  apply Finset.measurable_sum
  intro i _hi
  exact (measurable_lowerProjectedState_apply a b sample state hsample hstate i).mul
    (measurable_lowerProjectedState_apply a b sample state hsample hstate i)

/-- Upper-band energy is nonnegative even away from the gap domain. -/
theorem upperBandEnergy_nonneg
    (a b : Real) (A : HermitianMatrix ι) (x : ι → Real) :
    0 ≤ upperBandEnergy a b A x :=
  coordinateEnergy_nonneg _

/-- Lower-band energy is nonnegative even away from the gap domain. -/
theorem lowerBandEnergy_nonneg
    (a b : Real) (A : HermitianMatrix ι) (x : ι → Real) :
    0 ≤ lowerBandEnergy a b A x :=
  coordinateEnergy_nonneg _

/-- A real Hermitian idempotent has orthogonal range and complementary-range
components. -/
theorem hermitianIdempotent_projected_orthogonal
    (P : Matrix ι ι Real) (hP : P.IsHermitian)
    (hid : IsIdempotentElem P) (x : ι → Real) :
    (P *ᵥ x) ⬝ᵥ (((1 : Matrix ι ι Real) - P) *ᵥ x) = 0 := by
  have htranspose : Pᵀ = P := by
    ext i j
    have hij := congrArg (fun M : Matrix ι ι Real => M i j) hP
    simpa [Matrix.IsHermitian, Matrix.conjTranspose] using hij
  have hzero : P * ((1 : Matrix ι ι Real) - P) = 0 := by
    rw [mul_sub, mul_one, hid, sub_self]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, htranspose, hzero,
    Matrix.vecMul_zero, zero_dotProduct]

omit [DecidableEq ι] in
/-- Pythagorean identity for two orthogonal coordinate vectors. -/
theorem coordinateEnergy_add_of_orthogonal
    (u v : ι → Real) (horth : u ⬝ᵥ v = 0) :
    coordinateEnergy (u + v) = coordinateEnergy u + coordinateEnergy v := by
  unfold coordinateEnergy
  rw [add_dotProduct, dotProduct_add, dotProduct_add, horth]
  rw [dotProduct_comm v u, horth]
  ring

/-- On a separated spectrum, upper and lower projected states are orthogonal. -/
theorem upperProjectedState_orthogonal_lowerProjectedState
    {a b : Real} (hab : a < b) (A : HermitianMatrix ι)
    (hgap : HasSeparatedSpectrum a b A) (x : ι → Real) :
    upperProjectedState a b A x ⬝ᵥ lowerProjectedState a b A x = 0 := by
  rw [lowerProjectedState_eq_one_sub_mulVec]
  exact hermitianIdempotent_projected_orthogonal
    (upperClusterProjector a b A)
    (upperClusterProjector_isHermitian a b A)
    (upperClusterProjector_isIdempotentElem hab A hgap) x

/-- Exact upper-plus-lower spectral energy decomposition on the gap domain. -/
theorem upperBandEnergy_add_lowerBandEnergy
    {a b : Real} (hab : a < b) (A : HermitianMatrix ι)
    (hgap : HasSeparatedSpectrum a b A) (x : ι → Real) :
    upperBandEnergy a b A x + lowerBandEnergy a b A x =
      coordinateEnergy x := by
  have horth := upperProjectedState_orthogonal_lowerProjectedState
    hab A hgap x
  have hpyth := coordinateEnergy_add_of_orthogonal
    (upperProjectedState a b A x) (lowerProjectedState a b A x) horth
  rw [upperProjectedState_add_lowerProjectedState a b A x] at hpyth
  exact hpyth.symm

/-- For an exact orthogonal projector, projected squared norm equals its
quadratic-form observable. -/
theorem upperBandEnergy_eq_dotProduct_projected
    {a b : Real} (hab : a < b) (A : HermitianMatrix ι)
    (hgap : HasSeparatedSpectrum a b A) (x : ι → Real) :
    upperBandEnergy a b A x = x ⬝ᵥ upperProjectedState a b A x := by
  have horth := upperProjectedState_orthogonal_lowerProjectedState
    hab A hgap x
  have hsum := upperProjectedState_add_lowerProjectedState a b A x
  calc
    upperBandEnergy a b A x =
        upperProjectedState a b A x ⬝ᵥ upperProjectedState a b A x := rfl
    _ = (upperProjectedState a b A x + lowerProjectedState a b A x) ⬝ᵥ
        upperProjectedState a b A x := by
      rw [add_dotProduct, dotProduct_comm (lowerProjectedState a b A x), horth,
        add_zero]
    _ = x ⬝ᵥ upperProjectedState a b A x := by rw [hsum]

end

end ArchonPhysics.SpectralBandEnergyObservable
