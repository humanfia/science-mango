import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Finite-mode phase renormalization

This module isolates the exact algebra behind the interaction-picture change

`b k t = exp (I * theta k t) * a k t`.

Multiplication by this unit phase preserves every mode norm and squared norm,
and hence preserves finite observables built only from those squared norms.
The final theorems give the exact `HasDerivAt` product-rule formula, including
the elementary cancellation of an explicitly supplied linear phase term.

No assertion is made that a self-interaction term in a microscopic model has
the required form, is divergent, or that this change of variables proves a
kinetic limit.
-/

namespace ArchonPhysics.PhaseRenormalization

noncomputable section

/-- The complex unit phase associated with a real angle. -/
def phaseFactor (theta : Real) : Complex :=
  Complex.exp (Complex.I * theta)

/-- Multiplication of one complex amplitude by a real-angle phase. -/
def phaseRenormalize (theta : Real) (a : Complex) : Complex :=
  phaseFactor theta * a

/-- Pointwise phase renormalization of a family of complex modes. -/
def phaseRenormalizeModes {ι : Type*} (theta : ι → Real) (a : ι → Complex) :
    ι → Complex :=
  fun k => phaseRenormalize (theta k) (a k)

/-- Time-dependent, mode-wise phase renormalization. -/
def phaseRenormalizedPath {ι : Type*}
    (theta : Real → ι → Real) (a : Real → ι → Complex) : Real → ι → Complex :=
  fun t => phaseRenormalizeModes (theta t) (a t)

/-- A real-angle exponential lies on the complex unit circle. -/
@[simp] theorem norm_phaseFactor (theta : Real) :
    ‖phaseFactor theta‖ = 1 := by
  change ‖Complex.exp (Complex.I * (theta : Complex))‖ = 1
  exact Complex.norm_exp_I_mul_ofReal theta

/-- The squared norm of a real-angle exponential is one. -/
@[simp] theorem normSq_phaseFactor (theta : Real) :
    Complex.normSq (phaseFactor theta) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_phaseFactor]
  norm_num

/-- Phase renormalization preserves the norm of one mode. -/
@[simp] theorem norm_phaseRenormalize (theta : Real) (a : Complex) :
    ‖phaseRenormalize theta a‖ = ‖a‖ := by
  simp [phaseRenormalize]

/-- Phase renormalization preserves the squared norm of one mode. -/
@[simp] theorem normSq_phaseRenormalize (theta : Real) (a : Complex) :
    Complex.normSq (phaseRenormalize theta a) = Complex.normSq a := by
  simp [phaseRenormalize, Complex.normSq_mul]

/-- Total squared amplitude (finite wave-action observable). -/
def totalModeNormSq {ι : Type*} [Fintype ι] (a : ι → Complex) : Real :=
  ∑ k, Complex.normSq (a k)

/-- A finite weighted modal-energy observable.  No sign condition is needed
for its phase invariance. -/
def weightedModeEnergy {ι : Type*} [Fintype ι]
    (weight : ι → Real) (a : ι → Complex) : Real :=
  ∑ k, weight k * Complex.normSq (a k)

/-- The normalized squared-amplitude weight of one mode. -/
def normalizedModeWeight {ι : Type*} [Fintype ι]
    (a : ι → Complex) (k : ι) : Real :=
  Complex.normSq (a k) / totalModeNormSq a

/-- The finite `l1` distance between normalized squared-amplitude weights and
the uniform weights.  It is defined even when the total is zero; the phase
invariance below therefore needs no nonvanishing side condition. -/
def normalizedL1Observable {ι : Type*} [Fintype ι] (a : ι → Complex) : Real :=
  ∑ k, |normalizedModeWeight a k - (Fintype.card ι : Real)⁻¹|

/-- Every mode retains its squared amplitude under a mode-dependent phase. -/
@[simp] theorem normSq_phaseRenormalizeModes {ι : Type*}
    (theta : ι → Real) (a : ι → Complex) (k : ι) :
    Complex.normSq (phaseRenormalizeModes theta a k) = Complex.normSq (a k) := by
  simp [phaseRenormalizeModes]

/-- The finite total squared amplitude is phase invariant. -/
@[simp] theorem totalModeNormSq_phaseRenormalizeModes {ι : Type*} [Fintype ι]
    (theta : ι → Real) (a : ι → Complex) :
    totalModeNormSq (phaseRenormalizeModes theta a) = totalModeNormSq a := by
  simp [totalModeNormSq]

/-- Every finite weighted modal-energy sum is phase invariant. -/
@[simp] theorem weightedModeEnergy_phaseRenormalizeModes
    {ι : Type*} [Fintype ι] (weight theta : ι → Real) (a : ι → Complex) :
    weightedModeEnergy weight (phaseRenormalizeModes theta a) =
      weightedModeEnergy weight a := by
  simp [weightedModeEnergy]

/-- Each normalized squared-amplitude weight is phase invariant. -/
@[simp] theorem normalizedModeWeight_phaseRenormalizeModes
    {ι : Type*} [Fintype ι] (theta : ι → Real) (a : ι → Complex) (k : ι) :
    normalizedModeWeight (phaseRenormalizeModes theta a) k =
      normalizedModeWeight a k := by
  simp [normalizedModeWeight]

/-- The normalized finite `l1` observable is phase invariant. -/
@[simp] theorem normalizedL1Observable_phaseRenormalizeModes
    {ι : Type*} [Fintype ι] (theta : ι → Real) (a : ι → Complex) :
    normalizedL1Observable (phaseRenormalizeModes theta a) =
      normalizedL1Observable a := by
  simp [normalizedL1Observable]

/-- Exact derivative of a time-dependent unit phase. -/
theorem hasDerivAt_phaseFactor
    {theta : Real → Real} {theta' t : Real}
    (htheta : HasDerivAt theta theta' t) :
    HasDerivAt (fun s => phaseFactor (theta s))
      (phaseFactor (theta t) * (Complex.I * (theta' : Complex))) t := by
  have hargument :
      HasDerivAt (fun s : Real => Complex.I * (theta s : Complex))
        (Complex.I * (theta' : Complex)) t :=
    htheta.ofReal_comp.const_mul Complex.I
  simpa [phaseFactor] using hargument.cexp

/-- Product-rule formula for `b(t) = exp (I * theta(t)) * a(t)`. -/
theorem hasDerivAt_phaseRenormalize
    {theta : Real → Real} {a : Real → Complex}
    {theta' t : Real} {a' : Complex}
    (htheta : HasDerivAt theta theta' t) (ha : HasDerivAt a a' t) :
    HasDerivAt (fun s => phaseRenormalize (theta s) (a s))
      (phaseFactor (theta t) *
        (a' + (Complex.I * (theta' : Complex)) * a t)) t := by
  have hproduct := (hasDerivAt_phaseFactor htheta).mul ha
  change HasDerivAt ((fun s => phaseFactor (theta s)) * a)
    (phaseFactor (theta t) *
      (a' + (Complex.I * (theta' : Complex)) * a t)) t
  exact hproduct.congr_deriv (by ring)

/-- Mode-wise form of the exact derivative transformation. -/
theorem hasDerivAt_phaseRenormalizedMode
    {ι : Type*} {theta : Real → ι → Real} {a : Real → ι → Complex}
    {theta' : ι → Real} {a' : ι → Complex} {t : Real} (k : ι)
    (htheta : HasDerivAt (fun s => theta s k) (theta' k) t)
    (ha : HasDerivAt (fun s => a s k) (a' k) t) :
    HasDerivAt (fun s => phaseRenormalizedPath theta a s k)
      (phaseFactor (theta t k) *
        (a' k + (Complex.I * (theta' k : Complex)) * a t k)) t := by
  simpa [phaseRenormalizedPath, phaseRenormalizeModes] using
    hasDerivAt_phaseRenormalize htheta ha

/-- Purely algebraic cancellation corollary: if the supplied amplitude
derivative contains the displayed negative phase drift, the transformed
derivative is the phased residual.  This theorem does not assert that any
physical self-interaction has this form. -/
theorem hasDerivAt_phaseRenormalize_of_sub_phaseDrift
    {theta : Real → Real} {a : Real → Complex}
    {theta' t : Real} {residual : Complex}
    (htheta : HasDerivAt theta theta' t)
    (ha : HasDerivAt a
      (residual - (Complex.I * (theta' : Complex)) * a t) t) :
    HasDerivAt (fun s => phaseRenormalize (theta s) (a s))
      (phaseFactor (theta t) * residual) t := by
  exact (hasDerivAt_phaseRenormalize htheta ha).congr_deriv (by ring)

end

end ArchonPhysics.PhaseRenormalization
