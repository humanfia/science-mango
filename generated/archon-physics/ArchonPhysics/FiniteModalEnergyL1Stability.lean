import ArchonPhysics.NormalizedL1Stability
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite modal-energy `L1` stability from amplitude `L2` stability

For a finite family of amplitudes, this module proves the deterministic map

`a ↦ (k ↦ ‖a k‖²)`

is locally Lipschitz from amplitude `L2` to energy-spectrum `L1`:

`sum_k |‖a k‖² - ‖b k‖²|
  ≤ (‖a‖₂ + ‖b‖₂) ‖a-b‖₂`.

Normalized-profile and per-mode RMS corollaries make the estimate usable by
the F3 microscopic-to-observable layer.  In particular, an accumulated modal
RMS error of order `g`, together with uniform RMS amplitude bounds, gives a
per-mode modal-energy `L1` error of order `g`.

This is only observable stability.  It does not prove an `L2` estimate between
an exact microscopic flow and a leading or kinetic flow; such an estimate must
be supplied separately.
-/

namespace ArchonPhysics.FiniteModalEnergyL1Stability

open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.NormalizedL1Stability

noncomputable section

variable {Mode : Type} {E : Type*} [Fintype Mode] [NormedAddCommGroup E]

/-- Squared-norm modal-energy spectrum.  For `E = Complex`, this is
`Complex.normSq` mode by mode. -/
def modalEnergySpectrum (a : Mode → E) : Mode → Real :=
  fun k => ‖a k‖ ^ 2

/-- Finite amplitude `L2` norm, written without choosing a bundled Euclidean
space representation. -/
def amplitudeL2Norm (a : Mode → E) : Real :=
  Real.sqrt (∑ k, ‖a k‖ ^ 2)

/-- Finite amplitude `L2` distance. -/
def amplitudeL2Distance (a b : Mode → E) : Real :=
  Real.sqrt (∑ k, ‖a k - b k‖ ^ 2)

/-- Raw `L1` distance between the two squared-norm energy spectra. -/
def modalEnergyL1Distance (a b : Mode → E) : Real :=
  l1Distance
    (modalEnergySpectrum (Mode := Mode) (E := E) a)
    (modalEnergySpectrum (Mode := Mode) (E := E) b)

/-- `L1` distance between the normalized modal-energy spectra. -/
def normalizedModalEnergyL1Distance (a b : Mode → E) : Real :=
  l1Distance
    (normalizedWeights (modalEnergySpectrum (Mode := Mode) (E := E) a))
    (normalizedWeights (modalEnergySpectrum (Mode := Mode) (E := E) b))

omit [Fintype Mode] in
theorem modalEnergySpectrum_nonneg (a : Mode → E) (k : Mode) :
    0 ≤ modalEnergySpectrum (Mode := Mode) (E := E) a k := by
  exact sq_nonneg _

theorem amplitudeL2Norm_nonneg (a : Mode → E) :
    0 ≤ amplitudeL2Norm a :=
  Real.sqrt_nonneg _

theorem amplitudeL2Distance_nonneg (a b : Mode → E) :
    0 ≤ amplitudeL2Distance a b :=
  Real.sqrt_nonneg _

theorem modalEnergyL1Distance_nonneg (a b : Mode → E) :
    0 ≤ modalEnergyL1Distance a b := by
  unfold modalEnergyL1Distance l1Distance
  exact Finset.sum_nonneg fun _k _hk => abs_nonneg _

omit [Fintype Mode] in
/-- Pointwise polarization-free estimate for the squared norm. -/
theorem abs_modalEnergySpectrum_sub_le (a b : Mode → E) (k : Mode) :
    |modalEnergySpectrum (Mode := Mode) (E := E) a k -
      modalEnergySpectrum (Mode := Mode) (E := E) b k| ≤
      (‖a k‖ + ‖b k‖) * ‖a k - b k‖ := by
  unfold modalEnergySpectrum
  calc
    |‖a k‖ ^ 2 - ‖b k‖ ^ 2| =
        (‖a k‖ + ‖b k‖) * |‖a k‖ - ‖b k‖| := by
      rw [show ‖a k‖ ^ 2 - ‖b k‖ ^ 2 =
        (‖a k‖ + ‖b k‖) * (‖a k‖ - ‖b k‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ (‖a k‖ + ‖b k‖) * ‖a k - b k‖ :=
      mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le (a k) (b k))
        (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The central finite-dimensional estimate:
`energy L1 ≤ (amplitude L2 sizes) * amplitude L2 error`. -/
theorem modalEnergyL1Distance_le (a b : Mode → E) :
    modalEnergyL1Distance a b ≤
      (amplitudeL2Norm a + amplitudeL2Norm b) *
        amplitudeL2Distance a b := by
  calc
    modalEnergyL1Distance a b =
        ∑ k, |modalEnergySpectrum (Mode := Mode) (E := E) a k -
          modalEnergySpectrum (Mode := Mode) (E := E) b k| := rfl
    _ ≤ ∑ k, (‖a k‖ + ‖b k‖) * ‖a k - b k‖ :=
      Finset.sum_le_sum fun k _hk => abs_modalEnergySpectrum_sub_le a b k
    _ = (∑ k, ‖a k‖ * ‖a k - b k‖) +
        ∑ k, ‖b k‖ * ‖a k - b k‖ := by
      simp_rw [add_mul]
      exact Finset.sum_add_distrib
    _ ≤ Real.sqrt (∑ k, ‖a k‖ ^ 2) *
          Real.sqrt (∑ k, ‖a k - b k‖ ^ 2) +
        Real.sqrt (∑ k, ‖b k‖ ^ 2) *
          Real.sqrt (∑ k, ‖a k - b k‖ ^ 2) := by
      exact add_le_add
        (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun k => ‖a k‖) (fun k => ‖a k - b k‖))
        (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun k => ‖b k‖) (fun k => ‖a k - b k‖))
    _ = (amplitudeL2Norm a + amplitudeL2Norm b) *
        amplitudeL2Distance a b := by
      unfold amplitudeL2Norm amplitudeL2Distance
      ring

/-- A direct total-size/error-budget form of the central estimate. -/
theorem modalEnergyL1Distance_le_of_l2_bounds
    (a b : Mode → E) (amplitudeCeiling errorBound : Real)
    (hceiling : 0 ≤ amplitudeCeiling)
    (ha : amplitudeL2Norm a ≤ amplitudeCeiling)
    (hb : amplitudeL2Norm b ≤ amplitudeCeiling)
    (hab : amplitudeL2Distance a b ≤ errorBound) :
    modalEnergyL1Distance a b ≤
      2 * amplitudeCeiling * errorBound := by
  calc
    modalEnergyL1Distance a b ≤
        (amplitudeL2Norm a + amplitudeL2Norm b) *
          amplitudeL2Distance a b := modalEnergyL1Distance_le a b
    _ ≤ (amplitudeCeiling + amplitudeCeiling) * errorBound := by
      exact mul_le_mul (add_le_add ha hb) hab
        (amplitudeL2Distance_nonneg a b)
        (add_nonneg hceiling hceiling)
    _ = 2 * amplitudeCeiling * errorBound := by ring

/-! ## Normalized modal-energy profiles -/

/-- Raw amplitude stability followed by the existing normalization stability
bound.  The reference spectrum is `a`; hence its total appears below. -/
theorem normalizedModalEnergyL1Distance_le
    (a b : Mode → E)
    (haTotal : 0 < totalWeight (modalEnergySpectrum (Mode := Mode) (E := E) a))
    (hbTotal : 0 < totalWeight (modalEnergySpectrum (Mode := Mode) (E := E) b)) :
    normalizedModalEnergyL1Distance a b ≤
      2 * ((amplitudeL2Norm a + amplitudeL2Norm b) *
        amplitudeL2Distance a b) /
          totalWeight (modalEnergySpectrum (Mode := Mode) (E := E) a) := by
  calc
    normalizedModalEnergyL1Distance a b ≤
        2 * modalEnergyL1Distance a b /
          totalWeight (modalEnergySpectrum (Mode := Mode) (E := E) a) := by
      exact l1Distance_normalizedWeights_le
        (modalEnergySpectrum (Mode := Mode) (E := E) a)
        (modalEnergySpectrum (Mode := Mode) (E := E) b)
        haTotal hbTotal (modalEnergySpectrum_nonneg (Mode := Mode) (E := E) b)
    _ ≤ 2 * ((amplitudeL2Norm a + amplitudeL2Norm b) *
        amplitudeL2Distance a b) /
          totalWeight (modalEnergySpectrum (Mode := Mode) (E := E) a) := by
      gcongr
      exact modalEnergyL1Distance_le a b

/-- Version with a transparent lower bound on total reference energy. -/
theorem normalizedModalEnergyL1Distance_le_of_totalEnergyFloor
    (a b : Mode → E) (energyFloor : Real)
    (hfloor : 0 < energyFloor)
    (haFloor : energyFloor ≤ totalWeight (modalEnergySpectrum (Mode := Mode) (E := E) a))
    (hbTotal : 0 < totalWeight (modalEnergySpectrum (Mode := Mode) (E := E) b)) :
    normalizedModalEnergyL1Distance a b ≤
      (2 / energyFloor) *
        ((amplitudeL2Norm a + amplitudeL2Norm b) *
          amplitudeL2Distance a b) := by
  calc
    normalizedModalEnergyL1Distance a b ≤
        (2 / energyFloor) * modalEnergyL1Distance a b := by
      exact l1Distance_normalizedWeights_le_of_lowerBound
        (modalEnergySpectrum (Mode := Mode) (E := E) a)
        (modalEnergySpectrum (Mode := Mode) (E := E) b)
        hfloor haFloor hbTotal (modalEnergySpectrum_nonneg (Mode := Mode) (E := E) b)
    _ ≤ (2 / energyFloor) *
        ((amplitudeL2Norm a + amplitudeL2Norm b) *
          amplitudeL2Distance a b) := by
      exact mul_le_mul_of_nonneg_left (modalEnergyL1Distance_le a b)
        (div_nonneg (by norm_num) hfloor.le)

/-! ## Per-mode RMS form -/

/-- Per-mode RMS amplitude. -/
def amplitudeRMSNorm [Nonempty Mode] (a : Mode → E) : Real :=
  amplitudeL2Norm a / Real.sqrt (Fintype.card Mode : Real)

/-- Per-mode RMS amplitude error. -/
def amplitudeRMSDistance [Nonempty Mode] (a b : Mode → E) : Real :=
  amplitudeL2Distance a b / Real.sqrt (Fintype.card Mode : Real)

/-- Mean per-mode `L1` energy-spectrum error. -/
def perModeModalEnergyL1Distance [Nonempty Mode]
    (a b : Mode → E) : Real :=
  modalEnergyL1Distance a b / (Fintype.card Mode : Real)

theorem amplitudeRMSNorm_nonneg [Nonempty Mode] (a : Mode → E) :
    0 ≤ amplitudeRMSNorm a := by
  exact div_nonneg (amplitudeL2Norm_nonneg a) (Real.sqrt_nonneg _)

theorem amplitudeRMSDistance_nonneg [Nonempty Mode] (a b : Mode → E) :
    0 ≤ amplitudeRMSDistance a b := by
  exact div_nonneg (amplitudeL2Distance_nonneg a b) (Real.sqrt_nonneg _)

/-- Volume-normalized version of the central inequality. -/
theorem perModeModalEnergyL1Distance_le [Nonempty Mode]
    (a b : Mode → E) :
    perModeModalEnergyL1Distance a b ≤
      (amplitudeRMSNorm a + amplitudeRMSNorm b) *
        amplitudeRMSDistance a b := by
  have hcard : 0 < (Fintype.card Mode : Real) := by
    exact_mod_cast Fintype.card_pos
  have hsqrtCard : 0 < Real.sqrt (Fintype.card Mode : Real) :=
    Real.sqrt_pos.2 hcard
  calc
    perModeModalEnergyL1Distance a b ≤
        ((amplitudeL2Norm a + amplitudeL2Norm b) *
          amplitudeL2Distance a b) / (Fintype.card Mode : Real) := by
      exact div_le_div_of_nonneg_right (modalEnergyL1Distance_le a b) hcard.le
    _ = ((amplitudeL2Norm a / Real.sqrt (Fintype.card Mode : Real)) +
          (amplitudeL2Norm b / Real.sqrt (Fintype.card Mode : Real))) *
        (amplitudeL2Distance a b /
          Real.sqrt (Fintype.card Mode : Real)) := by
      field_simp [ne_of_gt hsqrtCard]
      rw [Real.sq_sqrt hcard.le]
    _ = (amplitudeRMSNorm a + amplitudeRMSNorm b) *
        amplitudeRMSDistance a b := rfl

/-- An accumulated modal RMS state error `≤ C g` transfers to an average
modal-energy error `≤ (A+B) C g` under RMS amplitude bounds. -/
theorem perModeModalEnergyL1Distance_le_of_rms_error
    [Nonempty Mode] (a b : Mode → E)
    (amplitudeCeilingA amplitudeCeilingB errorCoefficient g : Real)
    (_hA : 0 ≤ amplitudeCeilingA) (_hB : 0 ≤ amplitudeCeilingB)
    (hcoefficient : 0 ≤ errorCoefficient) (hg : 0 ≤ g)
    (ha : amplitudeRMSNorm a ≤ amplitudeCeilingA)
    (hb : amplitudeRMSNorm b ≤ amplitudeCeilingB)
    (hab : amplitudeRMSDistance a b ≤ errorCoefficient * g) :
    perModeModalEnergyL1Distance a b ≤
      (amplitudeCeilingA + amplitudeCeilingB) * errorCoefficient * g := by
  calc
    perModeModalEnergyL1Distance a b ≤
        (amplitudeRMSNorm a + amplitudeRMSNorm b) *
          amplitudeRMSDistance a b :=
      perModeModalEnergyL1Distance_le a b
    _ ≤ (amplitudeRMSNorm a + amplitudeRMSNorm b) *
        (errorCoefficient * g) := by
      exact mul_le_mul_of_nonneg_left hab
        (add_nonneg (amplitudeRMSNorm_nonneg a)
          (amplitudeRMSNorm_nonneg b))
    _ ≤ (amplitudeCeilingA + amplitudeCeilingB) *
        (errorCoefficient * g) := by
      exact mul_le_mul_of_nonneg_right (add_le_add ha hb)
        (mul_nonneg hcoefficient hg)
    _ = (amplitudeCeilingA + amplitudeCeilingB) *
        errorCoefficient * g := by ring

/-- If the total reference energy has the extensive lower bound
`card Mode * energyDensityFloor`, normalization cancels the volume factor and
the normalized spectrum is controlled by the per-mode energy error. -/
theorem normalizedModalEnergyL1Distance_le_of_energyDensityFloor
    [Nonempty Mode] (a b : Mode → E) (energyDensityFloor : Real)
    (hfloor : 0 < energyDensityFloor)
    (haFloor : (Fintype.card Mode : Real) * energyDensityFloor ≤
      totalWeight (modalEnergySpectrum (Mode := Mode) (E := E) a))
    (hbTotal : 0 < totalWeight (modalEnergySpectrum (Mode := Mode) (E := E) b)) :
    normalizedModalEnergyL1Distance a b ≤
      (2 / energyDensityFloor) * perModeModalEnergyL1Distance a b := by
  have hcard : 0 < (Fintype.card Mode : Real) := by
    exact_mod_cast Fintype.card_pos
  have hextensiveFloor :
      0 < (Fintype.card Mode : Real) * energyDensityFloor :=
    mul_pos hcard hfloor
  calc
    normalizedModalEnergyL1Distance a b ≤
        (2 / ((Fintype.card Mode : Real) * energyDensityFloor)) *
          modalEnergyL1Distance a b := by
      exact l1Distance_normalizedWeights_le_of_lowerBound
        (modalEnergySpectrum (Mode := Mode) (E := E) a)
        (modalEnergySpectrum (Mode := Mode) (E := E) b)
        hextensiveFloor haFloor hbTotal (modalEnergySpectrum_nonneg (Mode := Mode) (E := E) b)
    _ = (2 / energyDensityFloor) *
        perModeModalEnergyL1Distance a b := by
      unfold perModeModalEnergyL1Distance
      field_simp [ne_of_gt hcard, ne_of_gt hfloor]

/-- Combined normalized `O(g)` observable bound.  The amplitude ceilings are
square-root per-mode energy bounds; the denominator is the positive reference
energy-density floor. -/
theorem normalizedModalEnergyL1Distance_le_of_rms_error
    [Nonempty Mode] (a b : Mode → E)
    (energyDensityFloor amplitudeCeilingA amplitudeCeilingB
      errorCoefficient g : Real)
    (hfloor : 0 < energyDensityFloor)
    (hA : 0 ≤ amplitudeCeilingA) (hB : 0 ≤ amplitudeCeilingB)
    (hcoefficient : 0 ≤ errorCoefficient) (hg : 0 ≤ g)
    (haFloor : (Fintype.card Mode : Real) * energyDensityFloor ≤
      totalWeight (modalEnergySpectrum (Mode := Mode) (E := E) a))
    (hbTotal : 0 < totalWeight (modalEnergySpectrum (Mode := Mode) (E := E) b))
    (ha : amplitudeRMSNorm a ≤ amplitudeCeilingA)
    (hb : amplitudeRMSNorm b ≤ amplitudeCeilingB)
    (hab : amplitudeRMSDistance a b ≤ errorCoefficient * g) :
    normalizedModalEnergyL1Distance a b ≤
      (2 / energyDensityFloor) *
        ((amplitudeCeilingA + amplitudeCeilingB) *
          errorCoefficient * g) := by
  calc
    normalizedModalEnergyL1Distance a b ≤
        (2 / energyDensityFloor) * perModeModalEnergyL1Distance a b :=
      normalizedModalEnergyL1Distance_le_of_energyDensityFloor
        a b energyDensityFloor hfloor haFloor hbTotal
    _ ≤ (2 / energyDensityFloor) *
        ((amplitudeCeilingA + amplitudeCeilingB) *
          errorCoefficient * g) := by
      exact mul_le_mul_of_nonneg_left
        (perModeModalEnergyL1Distance_le_of_rms_error
          a b amplitudeCeilingA amplitudeCeilingB errorCoefficient g
          hA hB hcoefficient hg ha hb hab)
        (div_nonneg (by norm_num) hfloor.le)

end

end ArchonPhysics.FiniteModalEnergyL1Stability
