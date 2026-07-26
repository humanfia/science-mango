import Mathlib
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0521

open Dimension

/-!
# Exterior wave function of a finite step well

The primary image and the prose agree on the potential: there is an infinite
wall to the left of the origin, the potential vanishes on `0 < x < L`, and it
is the positive constant `U₀` for `x > L`.  The image's grey region lies under
the exterior `U₀` plateau; the auxiliary prose caption reverses the two finite
regions and is therefore not used as evidence.

Length, mass, energy, action, and inverse length are retained as unit-independent
physical quantities.  Real numbers below are explicitly coherent-SI readouts,
or the real coordinate used to evaluate the complex wave-function amplitude.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension of action, `mass * length² / time`. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A nonnegative, unit-independent inverse length (wave number). -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Joule-second readout of a physical action. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Inverse-metre readout of a physical wave number. -/
def waveNumberInInverseMeters (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber UnitChoices.SI).val : ℝ)

/-- The unit-independent physical zero of energy. -/
noncomputable def zeroPotentialEnergy : DimEnergy :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨0⟩

/-! ## Potential, setup, and primary-figure vocabulary -/

/-- A potential value is either a finite physical energy or an infinite wall. -/
inductive PotentialValue where
  | finite (energy : DimEnergy)
  | infinite

/-- Literal labels visible in the supplied potential-energy graph. -/
inductive FigureLabel where
  | potentialEnergyAxis
  | positionAxis
  | barrierHeight
  | origin
  | wellEdge
  | infiniteWall
  deriving DecidableEq, Fintype, Repr

/-! Qualitative and textual facts read from the primary raster. -/
structure SuppliedStepWellFigure where
  printedText : FigureLabel → String
  showsInfiniteWallAtOrigin : Bool
  showsZeroInteriorSegment : Bool
  showsUpwardStepAtWellEdge : Bool
  showsExteriorBarrierPlateau : Bool
  showsDashedBarrierHeightGuide : Bool
  shadesExteriorBarrierRegion : Bool

/-!
The independent physical quantities in the problem.  The coordinate argument
of `potentialAtMeterCoordinate` and `waveFunctionAmplitude` is a metre readout.
The energy called `E` in the source is kinetic energy in the zero-potential
interior, hence also the stationary state's total-energy readout.
-/
structure FiniteStepWellSetup where
  wellWidth : LengthQuantity
  barrierEnergy : DimEnergy
  particleMass : MassQuantity
  kineticEnergyInsideWell : DimEnergy
  reducedPlanckAction : ActionQuantity
  potentialAtMeterCoordinate : ℝ → PotentialValue
  waveFunctionAmplitude : ℝ → ℂ
  stateDeclaredTrapped : Bool
  figure : SuppliedStepWellFigure

/-!
The piecewise potential and trapped-state description stated in the prose and
confirmed by the primary image.  No exterior wave-function form or decay rate
occurs in this premise.
-/
structure MatchesFiniteStepWellScenario
    (setup : FiniteStepWellSetup) : Prop where
  infinitePotentialLeftOfOrigin :
    ∀ x, x < 0 → setup.potentialAtMeterCoordinate x = .infinite
  zeroPotentialInsideWell :
    ∀ x, 0 < x → x < lengthInMeters setup.wellWidth →
      setup.potentialAtMeterCoordinate x = .finite zeroPotentialEnergy
  barrierPotentialOutsideWell :
    ∀ x, lengthInMeters setup.wellWidth < x →
      setup.potentialAtMeterCoordinate x = .finite setup.barrierEnergy
  stateIsDeclaredTrapped : setup.stateDeclaredTrapped = true

/-! Every label and qualitative feature visible in image 521. -/
structure MatchesSuppliedStepWellFigure
    (setup : FiniteStepWellSetup) : Prop where
  potentialAxisText :
    setup.figure.printedText .potentialEnergyAxis = "U(x)"
  positionAxisText : setup.figure.printedText .positionAxis = "x"
  barrierHeightText : setup.figure.printedText .barrierHeight = "U₀"
  originText : setup.figure.printedText .origin = "0"
  wellEdgeText : setup.figure.printedText .wellEdge = "L"
  infiniteWallText : setup.figure.printedText .infiniteWall = "∞"
  infiniteWallShown : setup.figure.showsInfiniteWallAtOrigin = true
  zeroInteriorShown : setup.figure.showsZeroInteriorSegment = true
  upwardStepShown : setup.figure.showsUpwardStepAtWellEdge = true
  exteriorPlateauShown : setup.figure.showsExteriorBarrierPlateau = true
  dashedBarrierGuideShown :
    setup.figure.showsDashedBarrierHeightGuide = true
  exteriorBarrierShaded : setup.figure.shadesExteriorBarrierRegion = true

/-!
Positivity and ordering conditions on the physical parameters.  In particular,
`E < U₀` is source data, not the requested formula for `κ`.
-/
structure HasPhysicalFiniteStepWellParameters
    (setup : FiniteStepWellSetup) : Prop where
  wellWidthPositive : 0 < lengthInMeters setup.wellWidth
  particleMassPositive : 0 < massInKilograms setup.particleMass
  barrierEnergyPositive : 0 < energyInJoules setup.barrierEnergy
  kineticEnergyNonnegative :
    0 ≤ energyInJoules setup.kineticEnergyInsideWell
  kineticEnergyBelowBarrier :
    energyInJoules setup.kineticEnergyInsideWell <
      energyInJoules setup.barrierEnergy
  reducedPlanckActionPositive :
    0 < actionInJouleSeconds setup.reducedPlanckAction

/-!
Physlib's `Constants.ℏ` is the standard reduced Planck constant in
joule-seconds.  This calibration does not constrain the requested decay rate.
-/
structure UsesStandardReducedPlanckConstant
    (setup : FiniteStepWellSetup) : Prop where
  reducedPlanckActionSI :
    actionInJouleSeconds setup.reducedPlanckAction = (Constants.ℏ : ℝ)

/-! ## Governing equation and boundary condition -/

/--
The kinetic-plus-potential side of the one-dimensional stationary Schrödinger
equation in the exterior constant-potential region.
-/
noncomputable def exteriorSchrodingerLeftHandSide
    (setup : FiniteStepWellSetup) (x : ℝ) : ℂ :=
  Complex.ofReal
      (-(actionInJouleSeconds setup.reducedPlanckAction) ^ 2 /
        (2 * massInKilograms setup.particleMass)) *
      deriv (deriv setup.waveFunctionAmplitude) x +
    Complex.ofReal (energyInJoules setup.barrierEnergy) *
      setup.waveFunctionAmplitude x

/-!
Twice-continuous differentiability and the stationary Schrödinger equation on
`x > L`.  This is the governing law; it does not state an exponential ansatz
or a formula for its decay constant.
-/
structure SatisfiesExteriorStationarySchrodingerEquation
    (setup : FiniteStepWellSetup) : Prop where
  twiceContinuouslyDifferentiableOutside :
    ContDiffOn ℝ 2 setup.waveFunctionAmplitude
      (Set.Ioi (lengthInMeters setup.wellWidth))
  stationaryEquationOutside :
    ∀ x, lengthInMeters setup.wellWidth < x →
      exteriorSchrodingerLeftHandSide setup x =
        Complex.ofReal (energyInJoules setup.kineticEnergyInsideWell) *
          setup.waveFunctionAmplitude x

/-!
The wave function remains finite at positive infinity: beyond some exterior
cutoff its norm has a finite uniform bound.  This excludes a growing mode but
does not assume the requested decaying-exponential form or a zero limit.
-/
structure SatisfiesFiniteBoundaryConditionAtInfinity
    (setup : FiniteStepWellSetup) : Prop where
  eventuallyBoundedAtPositiveInfinity :
    ∃ cutoff bound : ℝ,
      lengthInMeters setup.wellWidth ≤ cutoff ∧
      0 ≤ bound ∧
      ∀ x, cutoff < x → ‖setup.waveFunctionAmplitude x‖ ≤ bound

/-!
For `E < U₀`, the exterior Schrödinger equation has growing and decaying real
exponential modes.  Finiteness at `+∞` removes the growing mode.  Thus the
exterior wave function is a single decaying exponential, with a positive
inverse-length `κ`, and it tends to zero.

The decay-rate relation below is the dimensionally consistent version of
recorded choice D:

`κ² = 2 m (U₀ - E) / ℏ²`.

The source chapter's plain-text answer choices display only `/ℏ`; that cannot
follow from the stated Schrödinger equation and has the wrong physical
dimension for `κ²`.

Blueprint: `thm:physics:phyx_mini_0521:target`.
-/
theorem exterior_waveFunction_has_decaying_exponential_form
    (setup : FiniteStepWellSetup)
    (_scenario : MatchesFiniteStepWellScenario setup)
    (_figure : MatchesSuppliedStepWellFigure setup)
    (_physical : HasPhysicalFiniteStepWellParameters setup)
    (_planck : UsesStandardReducedPlanckConstant setup)
    (_schrodinger : SatisfiesExteriorStationarySchrodingerEquation setup)
    (_boundary : SatisfiesFiniteBoundaryConditionAtInfinity setup) :
    ∃ (amplitude : ℂ) (κ : WaveNumberQuantity),
      0 < waveNumberInInverseMeters κ ∧
      waveNumberInInverseMeters κ ^ 2 =
        2 * massInKilograms setup.particleMass *
            (energyInJoules setup.barrierEnergy -
              energyInJoules setup.kineticEnergyInsideWell) /
          actionInJouleSeconds setup.reducedPlanckAction ^ 2 ∧
      (∀ x, lengthInMeters setup.wellWidth < x →
        setup.waveFunctionAmplitude x =
          amplitude * Complex.exp (Complex.ofReal
            (- waveNumberInInverseMeters κ *
              (x - lengthInMeters setup.wellWidth)))) ∧
      Filter.Tendsto setup.waveFunctionAmplitude Filter.atTop (nhds 0) := by
  let L := lengthInMeters setup.wellWidth
  let m := massInKilograms setup.particleMass
  let U := energyInJoules setup.barrierEnergy
  let E := energyInJoules setup.kineticEnergyInsideWell
  let h := actionInJouleSeconds setup.reducedPlanckAction
  let d := U - E
  let rateSq := 2 * m * d / h ^ 2
  have hm : 0 < m := _physical.particleMassPositive
  have hd : 0 < d := sub_pos.mpr _physical.kineticEnergyBelowBarrier
  have hh : 0 < h := _physical.reducedPlanckActionPositive
  have hrateSq : 0 < rateSq := by
    dsimp only [rateSq]
    positivity
  let k := Real.sqrt rateSq
  have hk : 0 < k := Real.sqrt_pos.2 hrateSq
  have hk_sq : k ^ 2 = rateSq := Real.sq_sqrt hrateSq.le
  let κ : WaveNumberQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI ⟨⟨k, hk.le⟩⟩
  have hκ : waveNumberInInverseMeters κ = k := by
    simp [κ, waveNumberInInverseMeters,
      CarriesDimension.toDimensionful_apply_apply]
    rfl
  have hode (x : ℝ) (hx : L < x) :
      deriv (deriv setup.waveFunctionAmplitude) x =
        (k ^ 2) • setup.waveFunctionAmplitude x := by
    have hs := _schrodinger.stationaryEquationOutside x hx
    rw [exteriorSchrodingerLeftHandSide] at hs
    change
      Complex.ofReal (-h ^ 2 / (2 * m)) *
            deriv (deriv setup.waveFunctionAmplitude) x +
          Complex.ofReal U * setup.waveFunctionAmplitude x =
        Complex.ofReal E * setup.waveFunctionAmplitude x at hs
    rw [← Complex.real_smul, ← Complex.real_smul,
      ← Complex.real_smul] at hs
    rw [hk_sq]
    change
      deriv (deriv setup.waveFunctionAmplitude) x =
        (2 * m * (U - E) / h ^ 2) • setup.waveFunctionAmplitude x
    have hm0 : m ≠ 0 := ne_of_gt hm
    have hh0 : h ≠ 0 := ne_of_gt hh
    have hrearr :
        (-h ^ 2 / (2 * m)) •
              deriv (deriv setup.waveFunctionAmplitude) x =
            E • setup.waveFunctionAmplitude x -
              U • setup.waveFunctionAmplitude x :=
      eq_sub_of_add_eq hs
    rw [← sub_smul] at hrearr
    have hmul :=
      congrArg (fun z : ℂ => (-(2 * m) / h ^ 2) • z) hrearr
    rw [smul_smul, smul_smul] at hmul
    have hleft :
        (-(2 * m) / h ^ 2) * (-h ^ 2 / (2 * m)) = 1 := by
      field_simp [hm0, hh0]
    have hright :
        (-(2 * m) / h ^ 2) * (E - U) =
          2 * m * (U - E) / h ^ 2 := by
      field_simp [hm0, hh0]
      ring
    rw [hleft, one_smul, hright] at hmul
    exact hmul
  have hclass :
      ∃ a b : ℂ, ∀ x, L < x →
        setup.waveFunctionAmplitude x =
          Real.exp (-k * x) • a + Real.exp (k * x) • b := by
    have hf : DifferentiableOn ℝ setup.waveFunctionAmplitude (Set.Ioi L) :=
      _schrodinger.twiceContinuouslyDifferentiableOutside.differentiableOn
        (by norm_num)
    have hdf_cd :
        ContDiffOn ℝ 1 (deriv setup.waveFunctionAmplitude) (Set.Ioi L) :=
      _schrodinger.twiceContinuouslyDifferentiableOutside.deriv_of_isOpen
        isOpen_Ioi (by norm_num)
    have hdf :
        DifferentiableOn ℝ (deriv setup.waveFunctionAmplitude) (Set.Ioi L) :=
      hdf_cd.differentiableOn (by norm_num)
    have hf_at (x : ℝ) (hx : L < x) :
        HasDerivAt setup.waveFunctionAmplitude
          (deriv setup.waveFunctionAmplitude x) x :=
      (hf x hx).differentiableAt (isOpen_Ioi.mem_nhds hx) |>.hasDerivAt
    have hdf_at (x : ℝ) (hx : L < x) :
        HasDerivAt (deriv setup.waveFunctionAmplitude)
          (deriv (deriv setup.waveFunctionAmplitude) x) x :=
      (hdf x hx).differentiableAt (isOpen_Ioi.mem_nhds hx) |>.hasDerivAt
    let A : ℝ → ℂ :=
      (fun x : ℝ => Real.exp (k * x)) •
        (k • setup.waveFunctionAmplitude -
          deriv setup.waveFunctionAmplitude)
    have hA_raw (x : ℝ) (hx : L < x) := by
      have hscale :
          HasDerivAt (fun y : ℝ => Real.exp (k * y))
            (Real.exp (k * x) * k) x := by
        simpa only [id_eq, mul_one, one_mul, mul_comm] using
          (((hasDerivAt_id x).const_mul k).exp)
      have hinner :=
        (hf_at x hx).const_smul k |>.sub (hdf_at x hx)
      exact hscale.smul hinner
    have hA_diff : DifferentiableOn ℝ A (Set.Ioi L) := fun x hx =>
      (hA_raw x hx).differentiableAt.differentiableWithinAt
    have hA_zero : Set.EqOn (deriv A) 0 (Set.Ioi L) := fun x hx => by
      have hderiv := (hA_raw x hx).deriv
      change deriv A x = 0
      rw [hderiv]
      change
        Real.exp (k * x) •
              (k • deriv setup.waveFunctionAmplitude x -
                deriv (deriv setup.waveFunctionAmplitude) x) +
            (Real.exp (k * x) * k) •
              (k • setup.waveFunctionAmplitude x -
                deriv setup.waveFunctionAmplitude x) =
          0
      rw [hode x hx]
      module
    have hA_const {x y : ℝ} (hx : L < x) (hy : L < y) :
        A x = A y :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hA_diff hA_zero hx hy
    let B : ℝ → ℂ :=
      (fun x : ℝ => Real.exp (-k * x)) •
        (k • setup.waveFunctionAmplitude +
          deriv setup.waveFunctionAmplitude)
    have hB_raw (x : ℝ) (hx : L < x) := by
      have hscale :
          HasDerivAt (fun y : ℝ => Real.exp (-k * y))
            (Real.exp (-k * x) * (-k)) x := by
        simpa only [id_eq, mul_one] using
          (((hasDerivAt_id x).const_mul (-k)).exp)
      have hinner :=
        (hf_at x hx).const_smul k |>.add (hdf_at x hx)
      exact hscale.smul hinner
    have hB_diff : DifferentiableOn ℝ B (Set.Ioi L) := fun x hx =>
      (hB_raw x hx).differentiableAt.differentiableWithinAt
    have hB_zero : Set.EqOn (deriv B) 0 (Set.Ioi L) := fun x hx => by
      have hderiv := (hB_raw x hx).deriv
      change deriv B x = 0
      rw [hderiv]
      change
        Real.exp (-k * x) •
              (k • deriv setup.waveFunctionAmplitude x +
                deriv (deriv setup.waveFunctionAmplitude) x) +
            (Real.exp (-k * x) * (-k)) •
              (k • setup.waveFunctionAmplitude x +
                deriv setup.waveFunctionAmplitude x) =
          0
      rw [hode x hx]
      module
    have hB_const {x y : ℝ} (hx : L < x) (hy : L < y) :
        B x = B y :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hB_diff hB_zero hx hy
    let x₀ := L + 1
    have hx₀ : L < x₀ := by
      dsimp only [x₀]
      linarith
    let a : ℂ := (1 / (2 * k)) • A x₀
    let b : ℂ := (1 / (2 * k)) • B x₀
    refine ⟨a, b, ?_⟩
    intro x hx
    have hAe := hA_const hx hx₀
    have hBe := hB_const hx hx₀
    have hA' :=
      congrArg (fun z : ℂ => Real.exp (-k * x) • z) hAe
    have hB' :=
      congrArg (fun z : ℂ => Real.exp (k * x) • z) hBe
    have hexpA :
        Real.exp (-k * x) * Real.exp (k * x) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    have hexpB :
        Real.exp (k * x) * Real.exp (-k * x) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    change
      Real.exp (-k * x) •
            (Real.exp (k * x) •
              (k • setup.waveFunctionAmplitude x -
                deriv setup.waveFunctionAmplitude x)) =
        Real.exp (-k * x) • A x₀ at hA'
    rw [smul_smul, hexpA, one_smul] at hA'
    change
      Real.exp (k * x) •
            (Real.exp (-k * x) •
              (k • setup.waveFunctionAmplitude x +
                deriv setup.waveFunctionAmplitude x)) =
        Real.exp (k * x) • B x₀ at hB'
    rw [smul_smul, hexpB, one_smul] at hB'
    have hsum :
        (k • setup.waveFunctionAmplitude x -
              deriv setup.waveFunctionAmplitude x) +
            (k • setup.waveFunctionAmplitude x +
              deriv setup.waveFunctionAmplitude x) =
          (2 * k) • setup.waveFunctionAmplitude x := by
      module
    have hk0 : k ≠ 0 := ne_of_gt hk
    calc
      setup.waveFunctionAmplitude x =
          (1 / (2 * k)) •
            ((k • setup.waveFunctionAmplitude x -
                deriv setup.waveFunctionAmplitude x) +
              (k • setup.waveFunctionAmplitude x +
                deriv setup.waveFunctionAmplitude x)) := by
            rw [hsum, smul_smul]
            field_simp
            simp
      _ = (1 / (2 * k)) •
            (Real.exp (-k * x) • A x₀ +
              Real.exp (k * x) • B x₀) := by
            rw [hA', hB']
      _ = Real.exp (-k * x) • a +
            Real.exp (k * x) • b := by
            dsimp only [a, b]
            module
  rcases hclass with ⟨a, b, hform⟩
  have hb : b = 0 := by
    rcases _boundary.eventuallyBoundedAtPositiveInfinity with
      ⟨cutoff, bound, _, _, hbound⟩
    have hf_bounded :
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (norm ∘ setup.waveFunctionAmplitude) := by
      refine ⟨bound, ?_⟩
      change ∀ᶠ x in Filter.atTop,
        ‖setup.waveFunctionAmplitude x‖ ≤ bound
      filter_upwards [Filter.eventually_ge_atTop (cutoff + 1)] with x hx
      exact hbound x (lt_of_lt_of_le (lt_add_one cutoff) hx)
    have hneg_arg :
        Filter.Tendsto (fun x : ℝ => -k * x)
          Filter.atTop Filter.atBot :=
      (Filter.tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hk)).2
        Filter.tendsto_id
    have hneg :
        Filter.Tendsto (fun x : ℝ => Real.exp (-k * x))
          Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hneg_arg
    let scaled : ℝ → ℂ :=
      (fun x : ℝ => Real.exp (-k * x)) •
        setup.waveFunctionAmplitude
    have hscaled_zero :
        Filter.Tendsto scaled Filter.atTop (nhds 0) := by
      exact
        NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
          hneg hf_bounded
    have hscaled_form :
        scaled =ᶠ[Filter.atTop]
          (fun x : ℝ => Real.exp ((-2 * k) * x) • a + b) := by
      filter_upwards [Filter.eventually_ge_atTop (L + 1)] with x hx
      have hxL : L < x := lt_of_lt_of_le (lt_add_one L) hx
      change
        Real.exp (-k * x) • setup.waveFunctionAmplitude x = _
      rw [hform x hxL, smul_add, smul_smul, smul_smul]
      have h1 :
          Real.exp (-k * x) * Real.exp (-k * x) =
            Real.exp ((-2 * k) * x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h2 :
          Real.exp (-k * x) * Real.exp (k * x) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
      rw [h1, h2, one_smul]
    have hneg2_arg :
        Filter.Tendsto (fun x : ℝ => (-2 * k) * x)
          Filter.atTop Filter.atBot :=
      (Filter.tendsto_const_mul_atBot_of_neg
        (by nlinarith : -2 * k < 0)).2 Filter.tendsto_id
    have hneg2 :
        Filter.Tendsto (fun x : ℝ => Real.exp ((-2 * k) * x))
          Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hneg2_arg
    have hright :
        Filter.Tendsto
          (fun x : ℝ => Real.exp ((-2 * k) * x) • a + b)
          Filter.atTop (nhds b) := by
      simpa using (hneg2.smul_const a).add_const b
    have hscaled_to_b :
        Filter.Tendsto scaled Filter.atTop (nhds b) :=
      hright.congr' hscaled_form.symm
    exact tendsto_nhds_unique hscaled_to_b hscaled_zero
  let amplitude : ℂ := Real.exp (-k * L) • a
  refine ⟨amplitude, κ, ?_, ?_, ?_, ?_⟩
  · rw [hκ]
    exact hk
  · rw [hκ, hk_sq]
  · intro x hx
    have hxL : L < x := hx
    rw [hκ]
    change
      setup.waveFunctionAmplitude x =
        amplitude * Complex.exp (Complex.ofReal (-k * (x - L)))
    rw [hform x hxL, hb, smul_zero, add_zero]
    dsimp only [amplitude]
    have hre :
        Real.exp (-k * x) =
          Real.exp (-k * L) * Real.exp (-k * (x - L)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hre, Complex.real_smul, Complex.real_smul,
      Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp]
    ring
  · have hneg_arg :
        Filter.Tendsto (fun x : ℝ => -k * x)
          Filter.atTop Filter.atBot :=
      (Filter.tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hk)).2
        Filter.tendsto_id
    have hneg :
        Filter.Tendsto (fun x : ℝ => Real.exp (-k * x))
          Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hneg_arg
    have hdecay :
        Filter.Tendsto (fun x : ℝ => Real.exp (-k * x) • a)
          Filter.atTop (nhds 0) := by
      simpa using hneg.smul_const a
    have hevent :
        setup.waveFunctionAmplitude =ᶠ[Filter.atTop]
          (fun x : ℝ => Real.exp (-k * x) • a) := by
      filter_upwards [Filter.eventually_ge_atTop (L + 1)] with x hx
      have hxL : L < x := lt_of_lt_of_le (lt_add_one L) hx
      rw [hform x hxL, hb, smul_zero, add_zero]
    exact hdecay.congr' hevent.symm

end PhyXMiniProblems.ProblemPhyXMini0521
