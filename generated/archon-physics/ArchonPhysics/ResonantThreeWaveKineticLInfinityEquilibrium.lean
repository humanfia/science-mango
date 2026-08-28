import ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
import ArchonPhysics.ResonantThreeWaveKineticEquilibrium

/-!
# Rayleigh--Jeans equilibrium in canonical L-infinity

This module lifts the pointwise RN Rayleigh--Jeans equilibrium to the genuine
canonical `L-infinity` quotient vector field.  It proves that the quotient
collision map is zero, hence the corresponding constant curve is a global
solution of the unclipped equation, and records its zero entropy production.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticLInfinityEquilibrium

open Filter MeasureTheory
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ResonantThreeWaveKineticEntropy
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- A positive-frequency Rayleigh--Jeans profile belongs to canonical
`L-infinity`. -/
theorem rayleighJeansMemLpTop
    (collision : ResonantThreeWaveMeasure Mode) (temperature : Real)
    (frequencyFloor : Real) (hfrequencyFloor : 0 < frequencyFloor)
    (hfrequency : ∀ mode, frequencyFloor ≤ collision.frequency mode) :
    MemLp (rayleighJeansAction temperature collision.frequency) ∞
      (collisionReferenceMeasure collision) := by
  have hbounded := rayleighJeansAction_isBoundedMeasurable collision temperature
    frequencyFloor hfrequencyFloor hfrequency
  obtain ⟨bound, hbound⟩ := hbounded.exists_norm_bound
  exact memLp_top_of_bound hbounded.measurable.aestronglyMeasurable bound
    (Filter.Eventually.of_forall hbound)

/-- The Rayleigh--Jeans profile as a canonical `L-infinity` quotient class. -/
def rayleighJeansClass
    (collision : ResonantThreeWaveMeasure Mode) (temperature : Real)
    (frequencyFloor : Real) (hfrequencyFloor : 0 < frequencyFloor)
    (hfrequency : ∀ mode, frequencyFloor ≤ collision.frequency mode) :
    CanonicalLInfinity collision :=
  (rayleighJeansMemLpTop collision temperature frequencyFloor
    hfrequencyFloor hfrequency).toLp
    (rayleighJeansAction temperature collision.frequency)

/-- The RN collision map vanishes exactly on the quotient Rayleigh--Jeans
class. -/
theorem collisionMap_rayleighJeansClass_eq_zero
    (collision : ResonantThreeWaveMeasure Mode) (temperature : Real)
    (htemperature : 0 < temperature)
    (frequencyFloor : Real) (hfrequencyFloor : 0 < frequencyFloor)
    (hfrequency : ∀ mode, frequencyFloor ≤ collision.frequency mode) :
    collisionMap collision
      (rayleighJeansClass collision temperature frequencyFloor
        hfrequencyFloor hfrequency) = 0 := by
  let action := rayleighJeansAction temperature collision.frequency
  let hmem := rayleighJeansMemLpTop collision temperature frequencyFloor
    hfrequencyFloor hfrequency
  let classAction := rayleighJeansClass collision temperature frequencyFloor
    hfrequencyFloor hfrequency
  have hbounded := rayleighJeansAction_isBoundedMeasurable collision temperature
    frequencyFloor hfrequencyFloor hfrequency
  obtain ⟨bound, hbound⟩ := hbounded.exists_norm_bound
  have hae : action =ᵐ[collisionReferenceMeasure collision] classAction := by
    exact (MemLp.coeFn_toLp hmem).symm
  have hmap : collisionMap collision classAction =
      (collisionVector_memLp_top_of_bound collision
        hbounded.measurable hbound).toLp
        (collisionVector collision action) :=
    collisionMap_eq_toLp_of_ae_eq collision classAction
      hbounded.measurable hbound hae
  rw [hmap]
  apply Lp.ext
  have hzero :=
    collisionVector_ae_eq_zero_of_inverseAction_eq_scale_frequency
      collision action temperature⁻¹
      (rayleighJeansAction_pos collision temperature htemperature
        frequencyFloor hfrequencyFloor hfrequency)
      (inverse_rayleighJeansAction temperature collision.frequency)
  filter_upwards [MemLp.coeFn_toLp
      (collisionVector_memLp_top_of_bound collision
        hbounded.measurable hbound), hzero,
    Lp.coeFn_zero Real ∞ (collisionReferenceMeasure collision)]
    with mode hcoe hz hzeroCoe
  rw [hcoe, hz, hzeroCoe]
  simp only [Pi.zero_apply]

/-- The quotient Rayleigh--Jeans state is a global stationary solution of the
unclipped coupling-scaled RN equation. -/
theorem rayleighJeansClass_global_stationary
    (collision : ResonantThreeWaveMeasure Mode) (g temperature : Real)
    (htemperature : 0 < temperature)
    (frequencyFloor : Real) (hfrequencyFloor : 0 < frequencyFloor)
    (hfrequency : ∀ mode, frequencyFloor ≤ collision.frequency mode) :
    let equilibrium := rayleighJeansClass collision temperature frequencyFloor
      hfrequencyFloor hfrequency
    (∀ t : Real, (fun _ : Real ↦ equilibrium) t = equilibrium) ∧
      ∀ t : Real, HasDerivAt (fun _ : Real ↦ equilibrium)
        (rnCollisionVectorField collision g equilibrium) t := by
  dsimp only
  constructor
  · intro t
    rfl
  · intro t
    have hmap := collisionMap_rayleighJeansClass_eq_zero collision temperature
      htemperature frequencyFloor hfrequencyFloor hfrequency
    rw [rnCollisionVectorField, hmap, smul_zero]
    exact hasDerivAt_const t _

/-- The same quotient equilibrium is connected to the existing continuum
entropy interface: its representative has zero log-entropy production. -/
theorem rayleighJeansClass_entropyProduction_eq_zero
    (collision : ResonantThreeWaveMeasure Mode) (temperature : Real)
    (htemperature : 0 < temperature)
    (frequencyFloor : Real) (hfrequencyFloor : 0 < frequencyFloor)
    (hfrequency : ∀ mode, frequencyFloor ≤ collision.frequency mode) :
    continuumLogEntropyProduction collision
      (rayleighJeansAction temperature collision.frequency) = 0 := by
  exact (rayleighJeans_rn_equilibrium collision temperature htemperature
    frequencyFloor hfrequencyFloor hfrequency).2.2.1

end

end ArchonPhysics.ResonantThreeWaveKineticLInfinityEquilibrium
