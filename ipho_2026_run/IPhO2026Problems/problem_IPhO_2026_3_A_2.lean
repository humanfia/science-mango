import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy

/-!
# IPhO 2026, problem 3, part A.2

This file models the incremental electromagnetic work supplied to the densely
wound, low-resistance coil around a thin paramagnetic torus.

All physical quantities below are dimensionful.  A scalar value at a choice of
units represents the approximately uniform magnitude (or signed increment)
specified in the problem.
-/

namespace IPhO2026Problems
namespace IPhO2026_3_A_2

open Dimension
open NNReal

/-- A nonnegative length magnitude, used for the radii shown in Fig. 3a. -/
abbrev DimLengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 ℝ≥0)

/-- A nonnegative volume magnitude. -/
abbrev DimVolumeMagnitude : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ≥0)

/-- Electric current, with dimension charge per time. -/
abbrev DimElectricCurrent : Type :=
  Dimensionful (WithDim (C𝓭 * T𝓭⁻¹) ℝ)

/-- Magnetic field strength `H`, with SI unit ampere per metre. -/
abbrev DimMagneticFieldStrength : Type :=
  Dimensionful (WithDim (C𝓭 * T𝓭⁻¹ * L𝓭⁻¹) ℝ)

/-- Magnetization `M`, which has the same dimension as `H`. -/
abbrev DimMagnetization : Type := DimMagneticFieldStrength

/-- Magnetic flux density `B`, with SI unit tesla. -/
abbrev DimMagneticFluxDensity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * C𝓭⁻¹) ℝ)

/-- A signed infinitesimal change `dB` of magnetic flux density. -/
abbrev DimMagneticFluxDensityIncrement : Type := DimMagneticFluxDensity

/-- Vacuum permeability, whose dimension makes `μ₀ H` a flux density. -/
abbrev DimVacuumPermeability : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹) ℝ)

/--
The time integral of the external source voltage during the infinitesimal
change.  It has the dimension of magnetic flux (`B` times area).
-/
abbrev DimVoltageImpulse : Type :=
  Dimensionful
    (WithDim ((M𝓭 * T𝓭⁻¹ * C𝓭⁻¹) * (L𝓭 * L𝓭)) ℝ)

/-- The real scalar readout of a signed dimensionful quantity in units `u`. -/
def signedReadout {d : Dimension}
    (q : Dimensionful (WithDim d ℝ)) (u : UnitChoices) : ℝ :=
  (q u).val

/-- The real scalar readout of a nonnegative dimensionful magnitude in units `u`. -/
def magnitudeReadout {d : Dimension}
    (q : Dimensionful (WithDim d ℝ≥0)) (u : UnitChoices) : ℝ :=
  ((q u).val : ℝ)

/--
Geometry and figure labels of the torus in Fig. 3a.  The figure labels the
mean radius by `R` and the circular cross-section diameter by `2r`.
-/
structure TorusGeometry where
  /-- Mean radius `R`. -/
  meanRadius : DimLengthMagnitude
  /-- Cross-section radius `r` (called the inner radius in the statement). -/
  innerRadius : DimLengthMagnitude
  /-- Cross-sectional area `A`. -/
  crossSectionArea : DimArea
  /-- Material volume `V`. -/
  volume : DimVolumeMagnitude

/--
The thin circular-torus approximation represented explicitly with a
dimensionless smallness scale `ε`.  The exact area and volume readouts are the
geometric data used after neglecting corrections of order `r / R`.
-/
def IsThinCircularTorus (g : TorusGeometry) (ε : ℝ) : Prop :=
  0 < ε ∧
  ε < 1 ∧
  (∀ u : UnitChoices,
    0 < magnitudeReadout g.meanRadius u ∧
    0 < magnitudeReadout g.innerRadius u ∧
    magnitudeReadout g.innerRadius u ≤
      ε * magnitudeReadout g.meanRadius u ∧
    magnitudeReadout g.crossSectionArea u =
      Real.pi * (magnitudeReadout g.innerRadius u) ^ 2 ∧
    magnitudeReadout g.volume u =
      2 * Real.pi * magnitudeReadout g.meanRadius u *
        magnitudeReadout g.crossSectionArea u)

/--
The idealized dense insulated winding.  Heating losses in the wire are
neglected; the only retained energy transfer is through the external source.
-/
structure IdealToroidalWinding where
  /-- Total number of turns `N`. -/
  turnCount : ℕ
  /-- Instantaneous signed current `I`. -/
  current : DimElectricCurrent

/--
The approximately uniform scalar magnetic state in the torus.  `H` and `M`
refer to their common toroidal direction, so nonnegative readouts encode the
parallel-paramagnetic convention.
-/
structure UniformMagneticState where
  /-- Uniform magnetic field strength magnitude `H`. -/
  fieldStrength : DimMagneticFieldStrength
  /-- Uniform magnetic flux density magnitude `B`. -/
  fluxDensity : DimMagneticFluxDensity
  /-- Uniform magnetization magnitude `M`. -/
  magnetization : DimMagnetization

/-- `M` is parallel to `H` in the scalar uniform-field model. -/
def IsAlignedParamagneticState (s : UniformMagneticState) : Prop :=
  ∀ u : UnitChoices,
    0 ≤ signedReadout s.fieldStrength u ∧
    0 ≤ signedReadout s.magnetization u

/-- The material relation `B = μ₀ H + μ₀ M`. -/
def SatisfiesParamagneticConstitutiveLaw
    (μ₀ : DimVacuumPermeability) (s : UniformMagneticState) : Prop :=
  ∀ u : UnitChoices,
    signedReadout s.fluxDensity u =
      signedReadout μ₀ u * signedReadout s.fieldStrength u +
      signedReadout μ₀ u * signedReadout s.magnetization u

/--
The reusable conclusion of part A.1, obtained from Ampère's law in the thin
uniform torus:

`H = N I A / V`.
-/
def SatisfiesThinTorusAmpereLaw
    (g : TorusGeometry) (w : IdealToroidalWinding)
    (s : UniformMagneticState) : Prop :=
  ∀ u : UnitChoices,
    signedReadout s.fieldStrength u =
      (w.turnCount : ℝ) * signedReadout w.current u *
        magnitudeReadout g.crossSectionArea u /
          magnitudeReadout g.volume u

/--
Faraday induction with the external voltage compensating the induced emf.
The source voltage impulse is therefore `N A dB` with the sign that increases
the torus flux density.
-/
def SatisfiesFaradayCompensationLaw
    (g : TorusGeometry) (w : IdealToroidalWinding)
    (dB : DimMagneticFluxDensityIncrement)
    (sourceVoltageImpulse : DimVoltageImpulse) : Prop :=
  ∀ u : UnitChoices,
    signedReadout sourceVoltageImpulse u =
      (w.turnCount : ℝ) * magnitudeReadout g.crossSectionArea u *
        signedReadout dB u

/--
Electrical work supplied by a lossless external source is current times the
source voltage impulse.  Positive `dWemf` means energy entering the
paramagnetic torus, as required by the problem's sign convention.
-/
def SatisfiesExternalSourceWorkLaw
    (w : IdealToroidalWinding)
    (sourceVoltageImpulse : DimVoltageImpulse)
    (dWemf : DimEnergy) : Prop :=
  ∀ u : UnitChoices,
    signedReadout dWemf u =
      signedReadout w.current u * signedReadout sourceVoltageImpulse u

/--
For a magnetic-flux-density change `dB`, the work performed by the external
voltage source is

`dW_emf = V H dB`.

The conclusion is stated for every choice of units.  The hypotheses contain
the constitutive, Ampère, Faraday, and source-work laws, but do not assume this
final relation.
-/
theorem externalSourceWorkIncrement_eq_volume_mul_fieldStrength_mul_fluxDensityIncrement
    (g : TorusGeometry)
    (ε : ℝ)
    (w : IdealToroidalWinding)
    (s : UniformMagneticState)
    (μ₀ : DimVacuumPermeability)
    (dB : DimMagneticFluxDensityIncrement)
    (sourceVoltageImpulse : DimVoltageImpulse)
    (dWemf : DimEnergy)
    (hGeometry : IsThinCircularTorus g ε)
    (hTurns : 0 < w.turnCount)
    (hAligned : IsAlignedParamagneticState s)
    (hConstitutive : SatisfiesParamagneticConstitutiveLaw μ₀ s)
    (hAmpere : SatisfiesThinTorusAmpereLaw g w s)
    (hFaraday :
      SatisfiesFaradayCompensationLaw g w dB sourceVoltageImpulse)
    (hSourceWork :
      SatisfiesExternalSourceWorkLaw w sourceVoltageImpulse dWemf) :
    ∀ u : UnitChoices,
      signedReadout dWemf u =
        magnitudeReadout g.volume u *
          signedReadout s.fieldStrength u * signedReadout dB u := by
  intro u
  rcases hGeometry with ⟨_, _, hGeometry⟩
  rcases hGeometry u with ⟨hR, hr, _, hA, hV⟩
  have hA_pos : 0 < magnitudeReadout g.crossSectionArea u := by
    rw [hA]
    positivity
  have hV_pos : 0 < magnitudeReadout g.volume u := by
    rw [hV]
    positivity
  rw [hSourceWork u, hFaraday u, hAmpere u]
  field_simp [ne_of_gt hV_pos]

end IPhO2026_3_A_2
end IPhO2026Problems
