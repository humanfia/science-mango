import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

/-!
# Transit time of a light ray through a parallel glass slab

This file formalizes the quantities shown in problem `phyx_mini_0003`.  Lengths,
times, and speeds are dimensionful PhysLean quantities.  Angles are
`Real.Angle`s, while refractive indices are dimensionless real numbers.
-/

namespace PhyXMini0003

open Dimension

/-- A physical length, represented independently of any particular choice of units. -/
abbrev DimLength := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time interval, represented independently of any particular choice of units. -/
abbrev DimTime := Dimensionful (WithDim T𝓭 ℝ)

/-- A real-valued physical speed, represented independently of any particular choice of units. -/
abbrev DimSpeedReal := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/--
The quantities in the parallel-sided glass-slab experiment.  The field
`lateralDisplacement` is the figure's distance labelled `d`; it is retained
even though no numerical value for it is supplied and it is not needed in the
final transit-time readout.
-/
structure ParallelGlassSlabExperiment where
  slabThickness : DimLength
  lateralDisplacement : DimLength
  pathLengthInGlass : DimLength
  transitTime : DimTime
  speedInGlass : DimSpeedReal
  incidentAngle : Real.Angle
  refractedAngle : Real.Angle
  emergentAngle : Real.Angle
  ambientRefractiveIndex : ℝ
  glassRefractiveIndex : ℝ

/--
The governing geometrical-optics laws used for this experiment.  They express
Snell's law, the refractive-index definition of the light speed, the projection
of the in-glass path onto the slab normal, uniform-speed transit, the lateral
shift geometry, and parallel emergence from the slab's parallel faces.
-/
structure ParallelGlassSlabGoverningLaws (e : ParallelGlassSlabExperiment) : Prop where
  ambient_index_pos : 0 < e.ambientRefractiveIndex
  glass_index_pos : 0 < e.glassRefractiveIndex
  refracted_angle_acute :
    0 ≤ e.refractedAngle.toReal ∧ e.refractedAngle.toReal < Real.pi / 2
  snell_law :
    e.ambientRefractiveIndex * Real.Angle.sin e.incidentAngle =
      e.glassRefractiveIndex * Real.Angle.sin e.refractedAngle
  speed_refractive_index_law : ∀ u : UnitChoices,
    (e.speedInGlass u).val * e.glassRefractiveIndex =
      (DimSpeed.speedOfLight u).val
  normal_projection_is_thickness : ∀ u : UnitChoices,
    (e.pathLengthInGlass u).val * Real.Angle.cos e.refractedAngle =
      (e.slabThickness u).val
  uniform_speed_transit : ∀ u : UnitChoices,
    (e.pathLengthInGlass u).val =
      (e.speedInGlass u).val * (e.transitTime u).val
  lateral_displacement_geometry : ∀ u : UnitChoices,
    (e.lateralDisplacement u).val * Real.Angle.cos e.refractedAngle =
      (e.slabThickness u).val *
        Real.Angle.sin (e.incidentAngle - e.refractedAngle)
  parallel_face_emergence : e.emergentAngle = e.incidentAngle

/--
Readouts taken from the problem statement and figure: air outside the slab,
glass index `1.50`, normal slab thickness `2.00 cm`, and incidence angle
`30.0°` from the normal.  The length readout is stated in SI units, hence
`2.00 cm = 2/100 m`.
-/
structure ParallelGlassSlabFigureReadouts (e : ParallelGlassSlabExperiment) : Prop where
  ambient_is_air : e.ambientRefractiveIndex = 1
  glass_index_readout : e.glassRefractiveIndex = (3 : ℝ) / 2
  thickness_readout_si : (e.slabThickness UnitChoices.SI).val = (2 : ℝ) / 100
  incidence_readout :
    e.incidentAngle = ((Real.pi / 6 : ℝ) : Real.Angle)

/--
For the figure data and geometrical-optics laws above, the time in seconds is
within half a unit in the last displayed digit of answer C,
`1.06 × 10⁻¹⁰ s`.  Thus the conclusion records the answer choice at its
stated three-significant-figure precision rather than asserting a false exact
equality with a rounded decimal.

Blueprint label: `thm:physics:phyx_mini_0003:target`.
-/
theorem transitTime_is_answer_C
    (e : ParallelGlassSlabExperiment)
    (_laws : ParallelGlassSlabGoverningLaws e)
    (_figure : ParallelGlassSlabFigureReadouts e) :
    |(e.transitTime UnitChoices.SI).val -
        (106 : ℝ) / 100 * 10 ^ (-10 : ℤ)| ≤
      (5 : ℝ) / 1000 * 10 ^ (-10 : ℤ) := by
  rcases _laws with
    ⟨hamb, hglass, hacute, hsnell, hspeed, hproj, htrans, hlat, hemerg⟩
  rcases _figure with ⟨hair, hindex, hthick, hinc⟩
  let t : ℝ := (e.transitTime UnitChoices.SI).val
  let c : ℝ := Real.Angle.cos e.refractedAngle
  change
    |t - (106 : ℝ) / 100 * 10 ^ (-10 : ℤ)| ≤
      (5 : ℝ) / 1000 * 10 ^ (-10 : ℤ)
  have hsin : Real.Angle.sin e.refractedAngle = (1 : ℝ) / 3 := by
    rw [hair, hindex, hinc, Real.Angle.sin_coe, Real.sin_pi_div_six] at hsnell
    nlinarith [hsnell]
  have hcospos : 0 < c := by
    dsimp [c]
    rw [Real.Angle.cos_pos_iff_abs_toReal_lt_pi_div_two,
      abs_of_nonneg hacute.1]
    exact hacute.2
  have hcos_sq : c ^ 2 = (8 : ℝ) / 9 := by
    dsimp [c]
    nlinarith [Real.Angle.cos_sq_add_sin_sq e.refractedAngle]
  have hv :
      (e.speedInGlass UnitChoices.SI).val = (599584916 : ℝ) / 3 := by
    have hs := hspeed UnitChoices.SI
    rw [hindex, DimSpeed.speedOfLight_in_SI] at hs
    norm_num at hs ⊢
    nlinarith [hs]
  have htc : t * c = (3 : ℝ) / (50 * 599584916) := by
    have hp := hproj UnitChoices.SI
    have ht := htrans UnitChoices.SI
    rw [hthick, ht, hv] at hp
    dsimp [t, c]
    norm_num at hp ⊢
    nlinarith [hp]
  have hprodpos : 0 < t * c := by
    rw [htc]
    norm_num
  have htpos : 0 < t := by
    rcases mul_pos_iff.mp hprodpos with h | h
    · exact h.1
    · exact (not_lt_of_ge hcospos.le h.2).elim
  have htc_sq := congrArg (fun x : ℝ => x ^ 2) htc
  rw [mul_pow, hcos_sq] at htc_sq
  norm_num at htc_sq
  have hl_sq : ((211 : ℝ) / 2000000000000) ^ 2 ≤ t ^ 2 := by
    nlinarith [htc_sq]
  have hu_sq : t ^ 2 ≤ ((213 : ℝ) / 2000000000000) ^ 2 := by
    nlinarith [htc_sq]
  have hl : (211 : ℝ) / 2000000000000 ≤ t :=
    (sq_le_sq₀ (by norm_num) htpos.le).mp hl_sq
  have hu : t ≤ (213 : ℝ) / 2000000000000 :=
    (sq_le_sq₀ htpos.le (by norm_num)).mp hu_sq
  rw [abs_le]
  norm_num
  constructor <;> linarith

end PhyXMini0003
