import Mathlib
import Physlib.Electromagnetism.Basic

namespace IPhO2026Problems
namespace IPhO2026_3_A_3

/-- A dimensionless small-parameter witness for the approximation `small ≪ large`.

The source does not prescribe a numerical cutoff for `r ≪ R`, so the ratio is
kept explicit rather than assigning an arbitrary bound such as `1 / 10`. -/
structure ScaleSeparation (small large : ℝ) where
  ratio : ℝ
  ratio_pos : 0 < ratio
  ratio_lt_one : ratio < 1
  small_eq_ratio_mul_large : small = ratio * large

/-- The homogeneous isotropic paramagnetic torus shown in Fig. 3a.

Every real-valued field is an SI scalar readout. The field
`innerRadius_r_m` is the source's `r`, shown through the diameter label `2r`.
-/
structure ParamagneticToroid where
  meanRadius_R_m : ℝ
  innerRadius_r_m : ℝ
  volume_V_m3 : ℝ
  crossSectionArea_A_m2 : ℝ
  meanRadius_pos : 0 < meanRadius_R_m
  innerRadius_pos : 0 < innerRadius_r_m
  volume_pos : 0 < volume_V_m3
  crossSectionArea_pos : 0 < crossSectionArea_A_m2
  thinToroid : ScaleSeparation innerRadius_r_m meanRadius_R_m
  circularCrossSection :
    crossSectionArea_A_m2 = Real.pi * innerRadius_r_m ^ 2
  volumeFromMeanPath :
    volume_V_m3 =
      (2 * Real.pi * meanRadius_R_m) * crossSectionArea_A_m2

/-- The dense insulated winding around the torus in Fig. 3a.

`turnCount_N` is dimensionless and `instantaneousCurrent_I_A` is its signed
instantaneous current readout in amperes.
-/
structure DenseInsulatedWinding where
  turnCount_N : ℕ
  instantaneousCurrent_I_A : ℝ
  turnCount_pos : 0 < turnCount_N
  current_nonneg : 0 ≤ instantaneousCurrent_I_A

/-- Uniform scalar magnetic readouts in the toroidal direction.

`H` and `M` are measured in amperes per metre and `B` in tesla. Their
nonnegativity records that the source formulates them as magnitudes; using one
toroidal direction also records the stated parallelism of `M` and `H`.
-/
structure UniformMagneticState where
  fieldStrength_H_A_per_m : ℝ
  fluxDensity_B_T : ℝ
  magnetization_M_A_per_m : ℝ
  fieldStrength_nonneg : 0 ≤ fieldStrength_H_A_per_m
  fluxDensity_nonneg : 0 ≤ fluxDensity_B_T
  magnetization_nonneg : 0 ≤ magnetization_M_A_per_m

/-- Signed infinitesimal magnetic readouts for the actual torus and its
vacuum-core reference.

The `dH` and `dM` components are in amperes per metre and both `dB` components
are in tesla.
-/
structure UniformMagneticIncrement where
  dFieldStrength_dH_A_per_m : ℝ
  dFluxDensity_dB_T : ℝ
  dMagnetization_dM_A_per_m : ℝ
  vacuumCore_dFluxDensity_dBvac_T : ℝ

/-- Signed work readouts in joules, all using the convention that energy
entering the paramagnetic torus is positive.
-/
structure WorkIncrementReadouts where
  sourceWork_dWemf_J : ℝ
  vacuumCoreWork_dWvac_J : ℝ
  materialWork_dW_J : ℝ

/-- Governing laws, the A.2 result, and the figure/model readouts needed for
the A.3 work subtraction.

Crucially, this predicate does not contain the requested closed form for
`materialWork_dW_J`.
-/
structure SatisfiesWorkModel
    (toroid : ParamagneticToroid)
    (winding : DenseInsulatedWinding)
    (state : UniformMagneticState)
    (change : UniformMagneticIncrement)
    (emSystem : Electromagnetism.EMSystem)
    (work : WorkIncrementReadouts) : Prop where
  vacuumPermeability_pos : 0 < emSystem.μ₀
  constitutiveLaw :
    state.fluxDensity_B_T =
      emSystem.μ₀ * state.fieldStrength_H_A_per_m
        + emSystem.μ₀ * state.magnetization_M_A_per_m
  incrementalConstitutiveLaw :
    change.dFluxDensity_dB_T =
      emSystem.μ₀ * change.dFieldStrength_dH_A_per_m
        + emSystem.μ₀ * change.dMagnetization_dM_A_per_m
  ampereLawForMeanToroidalLoop :
    state.fieldStrength_H_A_per_m
        * (2 * Real.pi * toroid.meanRadius_R_m) =
      (winding.turnCount_N : ℝ) * winding.instantaneousCurrent_I_A
  sourceWork_previousPart_A2 :
    work.sourceWork_dWemf_J =
      toroid.volume_V_m3 * state.fieldStrength_H_A_per_m
        * change.dFluxDensity_dB_T
  vacuumCoreIncrement :
    change.vacuumCore_dFluxDensity_dBvac_T =
      emSystem.μ₀ * change.dFieldStrength_dH_A_per_m
  vacuumCoreWork_from_A2 :
    work.vacuumCoreWork_dWvac_J =
      toroid.volume_V_m3 * state.fieldStrength_H_A_per_m
        * change.vacuumCore_dFluxDensity_dBvac_T
  sourceWork_partition :
    work.sourceWork_dWemf_J =
      work.vacuumCoreWork_dWvac_J + work.materialWork_dW_J

/-- **IPhO 2026 T3-A3.** After subtracting the work needed for the
corresponding vacuum-core field change, the signed work done on the
paramagnetic material is `μ₀ V H dM`.
-/
theorem materialWork_eq_mu0_mul_volume_mul_H_mul_dM
    (toroid : ParamagneticToroid)
    (winding : DenseInsulatedWinding)
    (state : UniformMagneticState)
    (change : UniformMagneticIncrement)
    (emSystem : Electromagnetism.EMSystem)
    (work : WorkIncrementReadouts)
    (hmodel :
      SatisfiesWorkModel toroid winding state change emSystem work) :
    work.materialWork_dW_J =
      emSystem.μ₀ * toroid.volume_V_m3 * state.fieldStrength_H_A_per_m
        * change.dMagnetization_dM_A_per_m := by
  calc
    work.materialWork_dW_J =
        work.sourceWork_dWemf_J - work.vacuumCoreWork_dWvac_J := by
      linarith [hmodel.sourceWork_partition]
    _ =
        toroid.volume_V_m3 * state.fieldStrength_H_A_per_m
            * change.dFluxDensity_dB_T
          - toroid.volume_V_m3 * state.fieldStrength_H_A_per_m
            * change.vacuumCore_dFluxDensity_dBvac_T := by
      rw [hmodel.sourceWork_previousPart_A2, hmodel.vacuumCoreWork_from_A2]
    _ =
        emSystem.μ₀ * toroid.volume_V_m3 * state.fieldStrength_H_A_per_m
          * change.dMagnetization_dM_A_per_m := by
      rw [hmodel.incrementalConstitutiveLaw, hmodel.vacuumCoreIncrement]
      ring

end IPhO2026_3_A_3
end IPhO2026Problems
