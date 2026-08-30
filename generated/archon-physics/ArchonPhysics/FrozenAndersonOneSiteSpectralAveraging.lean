import ArchonPhysics.FrozenAndersonDiagonalPotentialDensity
import ArchonPhysics.ShermanMorrisonRankOneResolvent
import ArchonPhysics.SingleMassThresholdCountSensitivity

/-!
# Frozen one-site Anderson spectral-averaging inputs

This module isolates the strongest finite-dimensional one-site statements
available without assuming a Wegner estimate or localization.  It sharpens
the frozen `Uniform[4/5, 6/5]` density constant to `5/2`, scalarizes the
Sherman--Morrison resolvent update to the exact local Green-function Mobius
law, and records oriented threshold-count interlacing for a diagonal site
update.

The remaining analytic step for a trace Wegner estimate is not hidden here:
one still needs a Poisson-kernel integral (or spectral-projection averaging)
for the complex local Green function, followed by the finite trace sum.
-/

namespace ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassAcousticCountingComparison
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.FrozenAndersonDiagonalPotentialDensity
open ArchonPhysics.ShermanMorrisonRankOneResolvent
open ArchonPhysics.SingleMassThresholdCountSensitivity
open MeasureTheory
open scoped ENNReal Matrix

noncomputable section

/-! ## Sharp density of the frozen one-site potential -/

/-- The exact uniform mass law has optimal global Lebesgue-density ceiling
`5/2`.  The earlier constant `3` remains a convenient coarse interface. -/
theorem massCoordinateLaw_le_fiveHalves_smul_volume :
    massCoordinateLaw ≤ (5 / 2 : ENNReal) • (volume : Measure Real) := by
  unfold massCoordinateLaw ProbabilityTheory.cond
  have hnormalization :
      ((volume : Measure Real) massSupport)⁻¹ ≤ (5 / 2 : ENNReal) := by
    simp [massSupport, massLower, massUpper, Real.volume_Icc]
    have hdifference : (6 / 5 : Real) - 4 / 5 = 2 / 5 := by norm_num
    rw [hdifference]
    rw [← ENNReal.ofReal_inv_of_pos
      (by norm_num : (0 : Real) < 2 / 5)]
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [Measure.le_iff']
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul hnormalization (Measure.restrict_le_self s)
    (by positivity) (by positivity)

/-- At nonzero squared frequency, the frozen Anderson diagonal potential has
the sharp density ceiling `5 / (2 |lambda|)`. -/
theorem andersonDiagonalPotentialLaw_le_fiveHalves_smul_volume
    {lambda : Real} (hlambda : lambda ≠ 0) :
    andersonDiagonalPotentialLaw lambda ≤
      ((5 / 2 : ENNReal) * ENNReal.ofReal |lambda|⁻¹) •
        (volume : Measure Real) := by
  unfold andersonDiagonalPotentialLaw
  let chart : Real → Real := andersonDiagonalPotential lambda
  have hchart : Measurable chart := by
    change Measurable (fun mass : Real ↦ lambda * mass)
    exact measurable_const.mul measurable_id
  calc
    Measure.map chart massCoordinateLaw ≤
        Measure.map chart ((5 / 2 : ENNReal) • (volume : Measure Real)) :=
      Measure.map_mono massCoordinateLaw_le_fiveHalves_smul_volume hchart
    _ = (5 / 2 : ENNReal) •
        Measure.map chart (volume : Measure Real) := by
      rw [Measure.map_smul]
    _ = (5 / 2 : ENNReal) •
        (ENNReal.ofReal |lambda|⁻¹ • (volume : Measure Real)) := by
      rw [map_andersonDiagonalPotential_volume hlambda]
    _ = ((5 / 2 : ENNReal) * ENNReal.ofReal |lambda|⁻¹) •
        (volume : Measure Real) := by
      rw [mul_smul]

/-- Sharp interval small-ball bound for the frozen diagonal potential. -/
theorem andersonDiagonalPotentialLaw_Icc_le_fiveHalves
    {lambda a b : Real} (hlambda : lambda ≠ 0) :
    andersonDiagonalPotentialLaw lambda (Set.Icc a b) ≤
      ((5 / 2 : ENNReal) * ENNReal.ofReal |lambda|⁻¹) *
        ENNReal.ofReal (b - a) := by
  have hmeasure := Measure.le_iff.mp
    (andersonDiagonalPotentialLaw_le_fiveHalves_smul_volume hlambda)
    (Set.Icc a b) measurableSet_Icc
  simpa [Measure.smul_apply, Real.volume_Icc] using hmeasure

/-! ## Scalar Sherman--Morrison law -/

/-- Bilinear matrix element of the nonsingular inverse.  For `u = v` this is
the local Green-function matrix element in the rank-one direction. -/
def bilinearResolventElement
    {field index : Type*} [Field field] [Fintype index] [DecidableEq index]
    (A : Matrix index index field) (u v : index → field) : field :=
  v ⬝ᵥ (A⁻¹ *ᵥ u)

/-- Exact Mobius law for the local inverse matrix element under a rank-one
update.  This is the scalar algebraic core of one-site spectral averaging. -/
theorem bilinearResolventElement_rankOne_update
    {field index : Type*} [Field field] [Fintype index] [DecidableEq index]
    (A : Matrix index index field) (hA : IsUnit A.det)
    (c : field) (u v : index → field)
    (hden : shermanMorrisonDenominator A c u v ≠ 0) :
    bilinearResolventElement (A + c • Matrix.vecMulVec u v) u v =
      bilinearResolventElement A u v /
        (1 + c * bilinearResolventElement A u v) := by
  let q : field := v ⬝ᵥ (A⁻¹ *ᵥ u)
  have hrow : (v ᵥ* A⁻¹) ⬝ᵥ u = q := by
    simpa [q] using (Matrix.dotProduct_mulVec v (A⁻¹) u).symm
  have hden' : 1 + c * q ≠ 0 := by
    simpa [shermanMorrisonDenominator, q] using hden
  have hden'' : 1 + q * c ≠ 0 := by
    simpa [mul_comm] using hden'
  rw [bilinearResolventElement, bilinearResolventElement]
  rw [nonsing_inv_rankOne_update A hA c u v hden]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec]
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul,
    op_smul_eq_mul]
  rw [hrow]
  simp only [shermanMorrisonDenominator]
  change q - c / (1 + c * q) * (q * q) = q / (1 + c * q)
  field_simp [hden', hden'']
  ring

/-- Version of the Mobius law whose denominator is discharged solely by
invertibility of the base and updated finite matrices. -/
theorem bilinearResolventElement_rankOne_update_of_isUnit_det
    {field index : Type*} [Field field] [Fintype index] [DecidableEq index]
    (A : Matrix index index field) (hA : IsUnit A.det)
    (c : field) (u v : index → field)
    (hupdate : IsUnit (A + c • Matrix.vecMulVec u v).det) :
    bilinearResolventElement (A + c • Matrix.vecMulVec u v) u v =
      bilinearResolventElement A u v /
        (1 + c * bilinearResolventElement A u v) :=
  bilinearResolventElement_rankOne_update A hA c u v
    (shermanMorrisonDenominator_ne_zero_of_isUnit_det_update
      A hA c u v hupdate)

/-- Away from a zero base Green element, taking a reciprocal linearizes the
rank-one resolvent dependence exactly. -/
theorem bilinearResolventElement_rankOne_update_inv
    {field index : Type*} [Field field] [Fintype index] [DecidableEq index]
    (A : Matrix index index field) (hA : IsUnit A.det)
    (c : field) (u v : index → field)
    (hbase : bilinearResolventElement A u v ≠ 0)
    (hden : shermanMorrisonDenominator A c u v ≠ 0) :
    (bilinearResolventElement
        (A + c • Matrix.vecMulVec u v) u v)⁻¹ =
      (bilinearResolventElement A u v)⁻¹ + c := by
  rw [bilinearResolventElement_rankOne_update A hA c u v hden]
  have hden' : 1 + c * bilinearResolventElement A u v ≠ 0 := by
    simpa [shermanMorrisonDenominator,
      bilinearResolventElement] using hden
  field_simp [hbase, hden']

/-! ## Finite real Anderson threshold counts -/

/-- Real coordinate vector at one finite site. -/
def realSiteVector {index : Type*} [DecidableEq index]
    (i : index) : index → Real :=
  Pi.single i 1

/-- A finite Hermitian background with one variable diagonal potential. -/
def oneSiteAndersonMatrix
    {index : Type*} [DecidableEq index]
    (background : Matrix index index Real) (i : index) (potential : Real) :
    Matrix index index Real :=
  background + potential •
    Matrix.vecMulVec (realSiteVector i) (realSiteVector i)

theorem oneSiteAndersonMatrix_isHermitian
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) (potential : Real) :
    (oneSiteAndersonMatrix background i potential).IsHermitian := by
  apply hbackground.add
  rw [Matrix.IsHermitian]
  simp [realSiteVector]

/-- Changing only the diagonal potential is exactly a positive rank-one
update whenever the new potential is larger. -/
theorem oneSiteAndersonMatrix_update
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (i : index) (x y : Real) :
    oneSiteAndersonMatrix background i y =
      oneSiteAndersonMatrix background i x +
        (y - x) • Matrix.vecMulVec (realSiteVector i) (realSiteVector i) := by
  unfold oneSiteAndersonMatrix
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- In every finite dimension, increasing one diagonal potential can only
decrease a sublevel spectral count, and changes it by at most one. -/
theorem oneSiteAndersonThresholdCount_sandwich
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) {x y : Real} (hxy : x ≤ y) (E : Real) :
    orderedEigenvalueThresholdCount
        ⟨oneSiteAndersonMatrix background i y,
          oneSiteAndersonMatrix_isHermitian background hbackground i y⟩ E ≤
      orderedEigenvalueThresholdCount
        ⟨oneSiteAndersonMatrix background i x,
          oneSiteAndersonMatrix_isHermitian background hbackground i x⟩ E ∧
    orderedEigenvalueThresholdCount
        ⟨oneSiteAndersonMatrix background i x,
          oneSiteAndersonMatrix_isHermitian background hbackground i x⟩ E ≤
      orderedEigenvalueThresholdCount
        ⟨oneSiteAndersonMatrix background i y,
          oneSiteAndersonMatrix_isHermitian background hbackground i y⟩ E + 1 := by
  exact orderedEigenvalueThresholdCount_positive_rankOne_update_sandwich
    (oneSiteAndersonMatrix background i x)
    (oneSiteAndersonMatrix background i y)
    (oneSiteAndersonMatrix_isHermitian background hbackground i x)
    (oneSiteAndersonMatrix_isHermitian background hbackground i y)
    (y - x) (sub_nonneg.mpr hxy) (realSiteVector i)
    (oneSiteAndersonMatrix_update background i x y) E

/-- Direct frozen-mass specialization: the variable site potential is
`lambda * mass`. -/
def frozenOneSiteAndersonMatrix
    {index : Type*} [DecidableEq index]
    (background : Matrix index index Real) (i : index)
    (lambda mass : Real) : Matrix index index Real :=
  oneSiteAndersonMatrix background i
    (andersonDiagonalPotential lambda mass)

/-- At nonnegative squared frequency, increasing a frozen mass gives the
oriented one-site spectral-count sandwich in every finite volume. -/
theorem frozenOneSiteAndersonThresholdCount_sandwich
    {index : Type*} [Fintype index] [DecidableEq index]
    (background : Matrix index index Real) (hbackground : background.IsHermitian)
    (i : index) {lambda mass mass' : Real}
    (hlambda : 0 ≤ lambda) (hmass : mass ≤ mass') (E : Real) :
    orderedEigenvalueThresholdCount
        ⟨frozenOneSiteAndersonMatrix background i lambda mass',
          oneSiteAndersonMatrix_isHermitian background hbackground i
            (andersonDiagonalPotential lambda mass')⟩ E ≤
      orderedEigenvalueThresholdCount
        ⟨frozenOneSiteAndersonMatrix background i lambda mass,
          oneSiteAndersonMatrix_isHermitian background hbackground i
            (andersonDiagonalPotential lambda mass)⟩ E ∧
    orderedEigenvalueThresholdCount
        ⟨frozenOneSiteAndersonMatrix background i lambda mass,
          oneSiteAndersonMatrix_isHermitian background hbackground i
            (andersonDiagonalPotential lambda mass)⟩ E ≤
      orderedEigenvalueThresholdCount
        ⟨frozenOneSiteAndersonMatrix background i lambda mass',
          oneSiteAndersonMatrix_isHermitian background hbackground i
            (andersonDiagonalPotential lambda mass')⟩ E + 1 := by
  apply oneSiteAndersonThresholdCount_sandwich background hbackground i
    (E := E)
  exact mul_le_mul_of_nonneg_left hmass hlambda

/-! ## Complex local Green function for the frozen site -/

/-- Complex coordinate vector at one finite site. -/
def complexSiteVector {index : Type*} [DecidableEq index]
    (i : index) : index → Complex :=
  Pi.single i 1

/-- If `baseShifted` is `z I` minus the frozen background operator, this is
the shifted finite Anderson matrix after inserting one real site potential. -/
def oneSiteAndersonShiftedMatrix
    {index : Type*} [DecidableEq index]
    (baseShifted : Matrix index index Complex) (i : index)
    (potential : Real) : Matrix index index Complex :=
  baseShifted - (potential : Complex) •
    Matrix.vecMulVec (complexSiteVector i) (complexSiteVector i)

theorem oneSiteAndersonShiftedMatrix_update
    {index : Type*} [Fintype index] [DecidableEq index]
    (baseShifted : Matrix index index Complex) (i : index) (x y : Real) :
    oneSiteAndersonShiftedMatrix baseShifted i y =
      oneSiteAndersonShiftedMatrix baseShifted i x +
        (-((y - x : Real) : Complex)) •
          Matrix.vecMulVec (complexSiteVector i) (complexSiteVector i) := by
  unfold oneSiteAndersonShiftedMatrix
  ext p q
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.ofReal_sub, neg_sub]
  ring

/-- The local diagonal Green element at the variable Anderson site. -/
def oneSiteAndersonLocalGreen
    {index : Type*} [Fintype index] [DecidableEq index]
    (baseShifted : Matrix index index Complex) (i : index)
    (potential : Real) : Complex :=
  bilinearResolventElement
    (oneSiteAndersonShiftedMatrix baseShifted i potential)
    (complexSiteVector i) (complexSiteVector i)

/-- Exact one-site local Green-function Mobius law.  The only hypotheses are
the two finite off-spectrum determinant certificates. -/
theorem oneSiteAndersonLocalGreen_eq_fraction
    {index : Type*} [Fintype index] [DecidableEq index]
    (baseShifted : Matrix index index Complex) (i : index) (x y : Real)
    (hbase : IsUnit (oneSiteAndersonShiftedMatrix baseShifted i x).det)
    (htarget : IsUnit (oneSiteAndersonShiftedMatrix baseShifted i y).det) :
    oneSiteAndersonLocalGreen baseShifted i y =
      oneSiteAndersonLocalGreen baseShifted i x /
        (1 - ((y - x : Real) : Complex) *
          oneSiteAndersonLocalGreen baseShifted i x) := by
  let B := oneSiteAndersonShiftedMatrix baseShifted i x
  let c : Complex := -((y - x : Real) : Complex)
  let e := complexSiteVector i
  have hupdate : oneSiteAndersonShiftedMatrix baseShifted i y =
      B + c • Matrix.vecMulVec e e := by
    simpa [B, c, e] using
      oneSiteAndersonShiftedMatrix_update baseShifted i x y
  have hunitUpdate : IsUnit (B + c • Matrix.vecMulVec e e).det := by
    rw [← hupdate]
    exact htarget
  have hden : shermanMorrisonDenominator B c e e ≠ 0 :=
    shermanMorrisonDenominator_ne_zero_of_isUnit_det_update
      B hbase c e e hunitUpdate
  have hmobius := bilinearResolventElement_rankOne_update
    B hbase c e e hden
  rw [← hupdate] at hmobius
  simpa only [oneSiteAndersonLocalGreen, B, c, e,
    neg_mul, sub_eq_add_neg] using hmobius

/-- Reciprocal form of the same law: the random site potential enters the
inverse local Green function with slope exactly `-1`. -/
theorem oneSiteAndersonLocalGreen_inv_eq
    {index : Type*} [Fintype index] [DecidableEq index]
    (baseShifted : Matrix index index Complex) (i : index) (x y : Real)
    (hbase : IsUnit (oneSiteAndersonShiftedMatrix baseShifted i x).det)
    (htarget : IsUnit (oneSiteAndersonShiftedMatrix baseShifted i y).det)
    (hgreen : oneSiteAndersonLocalGreen baseShifted i x ≠ 0) :
    (oneSiteAndersonLocalGreen baseShifted i y)⁻¹ =
      (oneSiteAndersonLocalGreen baseShifted i x)⁻¹ -
        ((y - x : Real) : Complex) := by
  let B := oneSiteAndersonShiftedMatrix baseShifted i x
  let c : Complex := -((y - x : Real) : Complex)
  let e := complexSiteVector i
  have hupdate : oneSiteAndersonShiftedMatrix baseShifted i y =
      B + c • Matrix.vecMulVec e e := by
    simpa [B, c, e] using
      oneSiteAndersonShiftedMatrix_update baseShifted i x y
  have hunitUpdate : IsUnit (B + c • Matrix.vecMulVec e e).det := by
    rw [← hupdate]
    exact htarget
  have hden : shermanMorrisonDenominator B c e e ≠ 0 :=
    shermanMorrisonDenominator_ne_zero_of_isUnit_det_update
      B hbase c e e hunitUpdate
  have hinv := bilinearResolventElement_rankOne_update_inv
    B hbase c e e hgreen hden
  rw [← hupdate] at hinv
  simpa only [oneSiteAndersonLocalGreen, B, c, e,
    sub_eq_add_neg] using hinv

/-- Frozen mass specialization of the local Green function. -/
def frozenOneSiteAndersonLocalGreen
    {index : Type*} [Fintype index] [DecidableEq index]
    (baseShifted : Matrix index index Complex) (i : index)
    (lambda mass : Real) : Complex :=
  oneSiteAndersonLocalGreen baseShifted i
    (andersonDiagonalPotential lambda mass)

/-- Direct frozen-`Uniform[4/5,6/5]` algebraic one-site averaging input: at
fixed environment the local Green function is a Mobius function of
`lambda * mass`. -/
theorem frozenOneSiteAndersonLocalGreen_eq_fraction
    {index : Type*} [Fintype index] [DecidableEq index]
    (baseShifted : Matrix index index Complex) (i : index)
    (lambda reference mass : Real)
    (hbase : IsUnit
      (oneSiteAndersonShiftedMatrix baseShifted i
        (andersonDiagonalPotential lambda reference)).det)
    (htarget : IsUnit
      (oneSiteAndersonShiftedMatrix baseShifted i
        (andersonDiagonalPotential lambda mass)).det) :
    frozenOneSiteAndersonLocalGreen baseShifted i lambda mass =
      frozenOneSiteAndersonLocalGreen baseShifted i lambda reference /
        (1 - ((andersonDiagonalPotential lambda mass -
          andersonDiagonalPotential lambda reference : Real) : Complex) *
            frozenOneSiteAndersonLocalGreen baseShifted i lambda reference) := by
  exact oneSiteAndersonLocalGreen_eq_fraction
    baseShifted i (andersonDiagonalPotential lambda reference)
      (andersonDiagonalPotential lambda mass) hbase htarget

end

end ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
