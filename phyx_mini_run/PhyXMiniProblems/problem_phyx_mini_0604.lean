import Mathlib
import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.TISE
import Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# Einstein heat capacity of a crystal

This file formalizes the physical model in problem `phyx_mini_0604`.  Energies,
angular frequencies, temperatures, and heat capacities use the scalar readouts
of the corresponding Physlib APIs in one consistent system of units.  The
separate figure readout below records that the plotted vertical axis instead
uses specific heat in `J g⁻¹ K⁻¹`.
-/

namespace PhyXMini0604

open MeasureTheory

/-- The three Cartesian directions explicitly named in the crystal model. -/
inductive CartesianAxis
  | x
  | y
  | z
  deriving DecidableEq, Fintype

/-- The two nearest-neighbor orientations along any Cartesian axis. -/
inductive AxisOrientation
  | negative
  | positive
  deriving DecidableEq, Fintype

/-- A nearest-neighbor direction is one of `±x`, `±y`, or `±z`. -/
abbrev NearestNeighborDirection := CartesianAxis × AxisOrientation

/-- There are six nearest-neighbor directions in the stated crystal geometry. -/
theorem nearestNeighborDirection_card : Fintype.card NearestNeighborDirection = 6 := by
  rfl

/-- Aggregate geometric data for the spring model of the crystal.

The equality `oscillatorCount = 3 * atomCount` records the sharing of each of
the six nearest-neighbor springs by the two atoms at its endpoints.
-/
structure CrystalGeometry where
  /-- Number `N` of atoms in the crystal. -/
  atomCount : ℕ
  atomCount_pos : 0 < atomCount
  /-- Number of atoms at the two ends of a nearest-neighbor spring. -/
  atomsPerSpring : ℕ
  atomsPerSpring_eq_two : atomsPerSpring = 2
  /-- Number of independent one-dimensional oscillators in the crystal. -/
  oscillatorCount : ℕ
  oscillatorCount_eq_three_mul_atoms : oscillatorCount = 3 * atomCount

/-- The Einstein model consists of identical one-dimensional quantum
oscillators and their discrete canonical ensemble.

The counting-measure and zero-degree-of-freedom fields express that `ℕ` labels
discrete quantum energy levels rather than a classical phase space.  The
current heat-capacity conclusion is deliberately not a field of this model.
-/
structure EinsteinCrystalModel where
  geometry : CrystalGeometry
  oscillator : QuantumMechanics.OneDimension.HarmonicOscillator
  ensemble : CanonicalEnsemble ℕ
  energy_quantized : ∀ n, ensemble.energy n = oscillator.eigenValue n
  counting_measure : ensemble.μ = Measure.count
  discrete_dof : ensemble.dof = 0
  unit_phaseSpace : ensemble.phaseSpaceunit = 1

/-- The Einstein temperature `Θ_E = ℏ ω / k_B`, as a temperature-valued scalar
readout in the units used by `Constants.kB`. -/
noncomputable def einsteinTemperature (model : EinsteinCrystalModel) : ℝ :=
  Constants.ℏ * model.oscillator.ω / Constants.kB

/-- The heat capacity per atom in the Einstein model.  Physlib's
`CanonicalEnsemble.heatCapacity` is `d Ē / dT` for one oscillator, and the
crystal has three such modes per atom. -/
noncomputable def heatCapacityPerAtom
    (model : EinsteinCrystalModel) (T : Temperature) : ℝ :=
  3 * model.ensemble.heatCapacity T

/-- The canonical partition function is the sum of Boltzmann weights over the
discrete oscillator levels. -/
theorem partitionFunction_eq_boltzmann_sum
    (model : EinsteinCrystalModel) (T : Temperature) :
    model.ensemble.partitionFunction T =
      ∑' n : ℕ, Real.exp (-((T.β : ℝ) * model.ensemble.energy n)) := by
  rw [model.ensemble.partitionFunction_dof_zero T model.discrete_dof,
    CanonicalEnsemble.mathematicalPartitionFunction_eq_integral, model.counting_measure]
  simp only [neg_mul]
  let f : ℕ → ℝ := fun n => Real.exp (-((T.β : ℝ) * model.ensemble.energy n))
  change (∫ n, f n ∂Measure.count) = ∑' n, f n
  by_cases hf : Summable f
  · have hfi : Integrable f Measure.count := MeasureTheory.integrable_count_iff.mpr (by
      simpa [Real.norm_eq_abs, abs_of_nonneg, f] using hf)
    simpa [f] using MeasureTheory.integral_countable hfi
  · rw [MeasureTheory.integral_undef, tsum_eq_zero_of_not_summable hf]
    intro hfi
    apply hf
    have hn := MeasureTheory.integrable_count_iff.mp hfi
    simpa [Real.norm_eq_abs, abs_of_nonneg, f] using hn

/-- The thermal probability of level `n` obeys the Boltzmann law.  This is a
classical random thermal probability; quantum mechanics enters only through
the quantized energy map in `EinsteinCrystalModel.energy_quantized`. -/
theorem probability_eq_boltzmann_weight
    (model : EinsteinCrystalModel) (T : Temperature) (n : ℕ) :
    model.ensemble.probability T n =
      Real.exp (-((T.β : ℝ) * model.ensemble.energy n)) /
        model.ensemble.partitionFunction T := by
  simpa [CanonicalEnsemble.probability] using
    congrArg (fun z =>
      Real.exp (-((T.β : ℝ) * model.ensemble.energy n)) / z)
      (model.ensemble.partitionFunction_dof_zero T model.discrete_dof).symm

/-- The mean energy of one quantized oscillator, including its temperature-
independent zero-point energy.  This is the statistical-mechanics input whose
temperature derivative gives the heat capacity. -/
theorem oscillator_meanEnergy_eq
    (model : EinsteinCrystalModel) (T : Temperature) (hT : 0 < T.val) :
    model.ensemble.meanEnergy T =
      Constants.ℏ * model.oscillator.ω / 2 +
        (Constants.ℏ * model.oscillator.ω) /
          (Real.exp (einsteinTemperature model / (T : ℝ)) - 1) := by
  let A : ℝ := Constants.ℏ * model.oscillator.ω
  let x : ℝ := einsteinTemperature model / (T : ℝ)
  let q : ℝ := Real.exp (-x)
  let c : ℝ := Real.exp (-x / 2)
  have hA : 0 < A := by
    exact mul_pos Constants.ℏ_pos model.oscillator.ω_pos
  have hTr : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hx : 0 < x := by
    dsimp [x, einsteinTemperature]
    exact div_pos
      (div_pos (mul_pos Constants.ℏ_pos model.oscillator.ω_pos) Constants.kB_pos) hTr
  have hβA : (T.β : ℝ) * A = x := by
    rw [Temperature.β_toReal]
    dsimp [A, x, einsteinTemperature]
    field_simp [Constants.kB_ne_zero, ne_of_gt hTr]
  have hE (n : ℕ) :
      model.ensemble.energy n = ((n : ℝ) + 1 / 2) * A := by
    rw [model.energy_quantized n]
    unfold QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue
    dsimp [A]
    ring
  have hq_pos : 0 < q := by
    exact Real.exp_pos _
  have hq_lt : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    linarith
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq_pos]
    exact hq_lt
  have hw (n : ℕ) :
      Real.exp (-((T.β : ℝ) * model.ensemble.energy n)) = c * q ^ n := by
    rw [hE n]
    have he :
        (T.β : ℝ) * (((n : ℝ) + 1 / 2) * A) = ((n : ℝ) + 1 / 2) * x := by
      rw [← hβA]
      ring
    rw [he]
    dsimp [c, q]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hsq : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_norm_lt_one hqnorm
  have hsn : Summable (fun n : ℕ => (n : ℝ) * q ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hqnorm).summable
  have hdenS :
      Summable (fun n : ℕ =>
        Real.exp (-((T.β : ℝ) * model.ensemble.energy n))) := by
    simpa only [hw] using hsq.mul_left c
  have hnterm (n : ℕ) :
      model.ensemble.energy n *
          Real.exp (-((T.β : ℝ) * model.ensemble.energy n)) =
        (A * c) * ((n : ℝ) * q ^ n) + (A * c / 2) * q ^ n := by
    rw [hw n, hE n]
    ring
  have hnumS :
      Summable (fun n : ℕ =>
        model.ensemble.energy n *
          Real.exp (-((T.β : ℝ) * model.ensemble.energy n))) := by
    simpa only [hnterm] using
      (hsn.mul_left (A * c)).add (hsq.mul_left (A * c / 2))
  have integrable_of_summable_nonneg
      {f : ℕ → ℝ} (hs : Summable f) (hf : ∀ n, 0 ≤ f n) :
      Integrable f Measure.count := by
    rw [MeasureTheory.integrable_count_iff]
    exact hs.congr (fun n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf n)])
  have hdenI :
      Integrable
        (fun n : ℕ => Real.exp (-((T.β : ℝ) * model.ensemble.energy n)))
        Measure.count :=
    integrable_of_summable_nonneg hdenS (fun _ => (Real.exp_pos _).le)
  have hnumI :
      Integrable
        (fun n : ℕ =>
          model.ensemble.energy n *
            Real.exp (-((T.β : ℝ) * model.ensemble.energy n)))
        Measure.count := by
    apply integrable_of_summable_nonneg hnumS
    intro n
    apply mul_nonneg
    · rw [hE n]
      positivity
    · exact (Real.exp_pos _).le
  rw [CanonicalEnsemble.meanEnergy_eq_ratio_of_integrals, model.counting_measure]
  simp only [neg_mul]
  rw [MeasureTheory.integral_countable hnumI, MeasureTheory.integral_countable hdenI]
  simp only [MeasureTheory.count_real_singleton, one_smul]
  rw [tsum_congr hnterm, tsum_congr hw]
  rw [(hsn.mul_left (A * c)).tsum_add (hsq.mul_left (A * c / 2)),
    tsum_mul_left, tsum_mul_left, tsum_mul_left,
    tsum_coe_mul_geometric_of_norm_lt_one hqnorm,
    tsum_geometric_of_norm_lt_one hqnorm]
  have hc : c ≠ 0 := ne_of_gt (Real.exp_pos _)
  have h1q : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq_lt)
  have hqne : q ≠ 0 := ne_of_gt hq_pos
  change
    (A * c * (q / (1 - q) ^ 2) + A * c / 2 * (1 - q)⁻¹) /
        (c * (1 - q)⁻¹) =
      A / 2 + A / (Real.exp x - 1)
  have hexp : Real.exp x = q⁻¹ := by
    dsimp [q]
    rw [Real.exp_neg]
    simp
  rw [hexp]
  field_simp [hc, h1q, hqne]
  all_goals ring

/-- **Blueprint target** `thm:physics:phyx_mini_0604:target`.

For positive absolute temperature, the heat capacity per atom of the Einstein
crystal has the stated closed form.
-/
theorem einstein_crystal_heat_capacity
    (model : EinsteinCrystalModel) (T : Temperature) (hT : 0 < T.val) :
    heatCapacityPerAtom model T =
      3 * Constants.kB * (einsteinTemperature model / (T : ℝ)) ^ 2 *
        Real.exp (einsteinTemperature model / (T : ℝ)) /
          (Real.exp (einsteinTemperature model / (T : ℝ)) - 1) ^ 2 := by
  let A : ℝ := Constants.ℏ * model.oscillator.ω
  let θ : ℝ := einsteinTemperature model
  let f : ℝ → ℝ := fun t => A / 2 + A / (Real.exp (θ / t) - 1)
  have hTr : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hA : 0 < A := by
    exact mul_pos Constants.ℏ_pos model.oscillator.ω_pos
  have hθ : 0 < θ := by
    dsimp [θ, einsteinTemperature, A] at hA ⊢
    exact div_pos hA Constants.kB_pos
  have hAθ : A = Constants.kB * θ := by
    dsimp [A, θ, einsteinTemperature]
    field_simp [Constants.kB_ne_zero]
  have hmean : Set.EqOn model.ensemble.meanEnergy_T f (Set.Ioi 0) := by
    intro t ht
    simpa [CanonicalEnsemble.meanEnergy_T, f, A, θ, Real.coe_toNNReal t ht.le] using
      oscillator_meanEnergy_eq model
        (Temperature.ofNNReal (Real.toNNReal t)) (Real.toNNReal_pos.mpr ht)
  have harg : 0 < θ / (T : ℝ) :=
    div_pos hθ hTr
  have hden : Real.exp (θ / (T : ℝ)) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr harg))
  have hg :
      HasDerivAt (fun t : ℝ => θ / t) (-θ / (T : ℝ) ^ 2) (T : ℝ) := by
    simpa only [div_eq_mul_inv, mul_neg, neg_mul] using
      (hasDerivAt_inv (ne_of_gt hTr)).const_mul θ
  have hd := hg.exp.sub_const 1
  have hfrac := (hasDerivAt_const (T : ℝ) A).div hd hden
  have hcoeff :
      (0 * (Real.exp (θ / (T : ℝ)) - 1) -
          A * (Real.exp (θ / (T : ℝ)) * (-θ / (T : ℝ) ^ 2))) /
          (Real.exp (θ / (T : ℝ)) - 1) ^ 2 =
        A * θ * Real.exp (θ / (T : ℝ)) /
          ((T : ℝ) ^ 2 * (Real.exp (θ / (T : ℝ)) - 1) ^ 2) := by
    field_simp [ne_of_gt hTr, hden]
    ring
  rw [hcoeff] at hfrac
  have hfder :
      HasDerivAt f
        (A * θ * Real.exp (θ / (T : ℝ)) /
          ((T : ℝ) ^ 2 * (Real.exp (θ / (T : ℝ)) - 1) ^ 2))
        (T : ℝ) := by
    simpa only [f, Pi.div_apply] using hfrac.const_add (A / 2)
  unfold heatCapacityPerAtom CanonicalEnsemble.heatCapacity
  change 3 * derivWithin model.ensemble.meanEnergy_T (Set.Ioi 0) (T : ℝ) = _
  rw [derivWithin_congr hmean (hmean hTr)]
  rw [hfder.hasDerivWithinAt.derivWithin (isOpen_Ioi.uniqueDiffWithinAt hTr)]
  change
    3 * (A * θ * Real.exp (θ / (T : ℝ)) /
        ((T : ℝ) ^ 2 * (Real.exp (θ / (T : ℝ)) - 1) ^ 2)) =
      3 * Constants.kB * (θ / (T : ℝ)) ^ 2 * Real.exp (θ / (T : ℝ)) /
        (Real.exp (θ / (T : ℝ)) - 1) ^ 2
  rw [hAθ]
  field_simp [ne_of_gt hTr, hden]

/-- The classical equipartition expression `Ē = k_B T` for one oscillator,
viewed as a real-valued function so that its temperature derivative is defined. -/
noncomputable def classicalOscillatorMeanEnergy (temperature : ℝ) : ℝ :=
  Constants.kB * temperature

/-- Classical heat capacity per atom, again with three oscillator modes per
atom and with the derivative restricted to positive temperatures. -/
noncomputable def classicalHeatCapacityPerAtom (T : Temperature) : ℝ :=
  3 * derivWithin classicalOscillatorMeanEnergy (Set.Ioi 0) (T : ℝ)

/-- The classical model predicts the temperature-independent value `3 k_B`. -/
theorem classical_heat_capacity
    (T : Temperature) (hT : 0 < T.val) :
    classicalHeatCapacityPerAtom T = 3 * Constants.kB := by
  unfold classicalHeatCapacityPerAtom classicalOscillatorMeanEnergy
  convert congrArg (fun x : ℝ => 3 * x)
    (((hasDerivAt_id (T : ℝ)).const_mul Constants.kB).hasDerivWithinAt.derivWithin
      (isOpen_Ioi.uniqueDiffWithinAt (by exact_mod_cast hT))) using 1 <;> simp

/-- The two curve labels visible in the auxiliary specific-heat figure. -/
inductive SpecificHeatCurve
  /-- The curve labeled `Cᵥ`, for constant-volume specific heat. -/
  | constantVolume
  /-- The curve labeled `Cₚ`, for constant-pressure specific heat. -/
  | constantPressure
  deriving DecidableEq

/-- Marker styles used to distinguish the two plotted curves. -/
inductive FigureMarker
  | solidCircle
  | openCircle
  deriving DecidableEq

/-- Direct readout of the auxiliary figure's axes and legend.

Axis values are numerical readouts: kelvin horizontally and `J g⁻¹ K⁻¹`
vertically.  They are metadata and are not hypotheses of the Einstein formula.
-/
structure SpecificHeatFigureReadout where
  temperatureMinKelvin : ℝ
  temperatureMaxKelvin : ℝ
  specificHeatMinJPerGramKelvin : ℝ
  specificHeatMaxJPerGramKelvin : ℝ
  marker : SpecificHeatCurve → FigureMarker

/-- Readout of figure 604.  The image extends to approximately `1100 K`, even
though its last numbered horizontal tick is `1000 K`. -/
def figure604Readout : SpecificHeatFigureReadout where
  temperatureMinKelvin := 0
  temperatureMaxKelvin := 1100
  specificHeatMinJPerGramKelvin := 0
  specificHeatMaxJPerGramKelvin := 2
  marker
    | .constantVolume => .solidCircle
    | .constantPressure => .openCircle

end PhyXMini0604
