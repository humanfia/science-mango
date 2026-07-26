import Mathlib
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0617

open Dimension

/-!
# Bound-state wave function beyond a finite step well

The supplied graph shows an infinite wall for `x < 0`, zero potential on
`0 < x < L`, and the constant positive barrier `U₀` for `x > L`.  Position
arguments below are coherent-SI metre readouts.  Length, mass, energy, action,
and inverse length remain dimensionful physical quantities.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative physical length, independent of the choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass, independent of the choice of units. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension of action, `mass * length² / time`. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative physical action, used for the reduced Planck constant. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A nonnegative inverse length, the dimension carried by `κ`. -/
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

/-- The unit-independent physical zero of potential energy. -/
noncomputable def zeroPotentialEnergy : DimEnergy :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨0⟩

/-! ## Potential well and primary-figure data -/

/-- A point of the potential is either a finite energy or an infinite wall. -/
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

/-- Qualitative and textual readouts from the supplied raster image. -/
structure SuppliedPotentialWellFigure where
  printedText : FigureLabel → String
  showsInfiniteWallAtOrigin : Bool
  showsZeroInteriorSegment : Bool
  showsUpwardStepAtWellEdge : Bool
  showsExteriorBarrierPlateau : Bool
  showsDashedBarrierHeightGuide : Bool
  shadesPotentialRegions : Bool

/-!
The independent physical data.  The source's kinetic energy `E` is measured
in the zero-potential interior and hence is also the stationary-state energy.
The wave function has complex amplitude, while its argument is a metre readout.
-/
structure FinitePotentialWellSetup where
  wellWidth : LengthQuantity
  barrierEnergy : DimEnergy
  particleMass : MassQuantity
  kineticEnergyInsideWell : DimEnergy
  reducedPlanckAction : ActionQuantity
  potentialAtMeterCoordinate : ℝ → PotentialValue
  waveFunctionAmplitude : ℝ → ℂ
  stateDeclaredTrapped : Bool
  figure : SuppliedPotentialWellFigure

/-!
The piecewise potential stated in the problem.  This premise contains no
exponential ansatz and no information about a coefficient or decay rate.
-/
structure MatchesPotentialWellScenario
    (setup : FinitePotentialWellSetup) : Prop where
  infinitePotentialLeftOfOrigin :
    ∀ x, x < 0 → setup.potentialAtMeterCoordinate x = .infinite
  zeroPotentialInsideWell :
    ∀ x, 0 < x → x < lengthInMeters setup.wellWidth →
      setup.potentialAtMeterCoordinate x = .finite zeroPotentialEnergy
  barrierPotentialOutsideWell :
    ∀ x, lengthInMeters setup.wellWidth < x →
      setup.potentialAtMeterCoordinate x = .finite setup.barrierEnergy
  stateIsDeclaredTrapped : setup.stateDeclaredTrapped = true

/-- Text and qualitative facts read directly from image `617.png`. -/
structure MatchesSuppliedPotentialWellFigure
    (setup : FinitePotentialWellSetup) : Prop where
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
  potentialRegionsShaded : setup.figure.shadesPotentialRegions = true

/-!
The source conditions `m > 0`, `U₀ > 0`, and `0 ≤ E < U₀`, together with
the positivity of `L` and `ℏ`.  These are parameter facts rather than any part
of the requested exterior wave-function formula.
-/
structure HasPhysicalPotentialWellParameters
    (setup : FinitePotentialWellSetup) : Prop where
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

/-- Calibration of the setup's action parameter to Physlib's standard `ℏ`. -/
structure UsesStandardReducedPlanckConstant
    (setup : FinitePotentialWellSetup) : Prop where
  reducedPlanckActionSI :
    actionInJouleSeconds setup.reducedPlanckAction = (Constants.ℏ : ℝ)

/-! ## Governing law and boundary condition -/

/--
The kinetic-plus-potential side of the stationary one-dimensional
Schrödinger equation in the exterior constant-potential region.
-/
noncomputable def exteriorSchrodingerLeftHandSide
    (setup : FinitePotentialWellSetup) (x : ℝ) : ℂ :=
  Complex.ofReal
      (-(actionInJouleSeconds setup.reducedPlanckAction) ^ 2 /
        (2 * massInKilograms setup.particleMass)) *
      deriv (deriv setup.waveFunctionAmplitude) x +
    Complex.ofReal (energyInJoules setup.barrierEnergy) *
      setup.waveFunctionAmplitude x

/-!
Twice-continuous differentiability and the stationary Schrödinger equation
on `x > L`.  This governing-law premise does not assume an exponential form.
-/
structure SatisfiesExteriorStationarySchrodingerEquation
    (setup : FinitePotentialWellSetup) : Prop where
  twiceContinuouslyDifferentiableOutside :
    ContDiffOn ℝ 2 setup.waveFunctionAmplitude
      (Set.Ioi (lengthInMeters setup.wellWidth))
  stationaryEquationOutside :
    ∀ x, lengthInMeters setup.wellWidth < x →
      exteriorSchrodingerLeftHandSide setup x =
        Complex.ofReal (energyInJoules setup.kineticEnergyInsideWell) *
          setup.waveFunctionAmplitude x

/-!
The stated boundary condition that the wave function remains finite toward
positive infinity, represented without assuming a limit or an exponential
ansatz: its norm is uniformly bounded beyond some exterior cutoff.
-/
structure SatisfiesFiniteBoundaryConditionAtInfinity
    (setup : FinitePotentialWellSetup) : Prop where
  eventuallyBoundedAtPositiveInfinity :
    ∃ cutoff bound : ℝ,
      lengthInMeters setup.wellWidth ≤ cutoff ∧
      0 ≤ bound ∧
      ∀ x, cutoff < x → ‖setup.waveFunctionAmplitude x‖ ≤ bound

/-!
For `E < U₀`, the exterior equation has the two modes displayed in recorded
choice A, `C e^(κx) + D e^(-κx)`.  The finite-at-infinity boundary condition
then forces the growing-mode coefficient `C` to vanish, leaving a decaying
exponential.  The relation for `κ²` records the inverse-length scale dictated by
the Schrödinger equation rather than assuming it in the physics premises.

Blueprint: `thm:physics:phyx_mini_0617:target`.
-/
theorem exterior_waveFunction_has_choice_A_form
    (setup : FinitePotentialWellSetup)
    (_scenario : MatchesPotentialWellScenario setup)
    (_figure : MatchesSuppliedPotentialWellFigure setup)
    (_physical : HasPhysicalPotentialWellParameters setup)
    (_planck : UsesStandardReducedPlanckConstant setup)
    (_schrodinger : SatisfiesExteriorStationarySchrodingerEquation setup)
    (_boundary : SatisfiesFiniteBoundaryConditionAtInfinity setup) :
    ∃ (C D : ℂ) (κ : WaveNumberQuantity),
      0 < waveNumberInInverseMeters κ ∧
      waveNumberInInverseMeters κ ^ 2 =
        2 * massInKilograms setup.particleMass *
            (energyInJoules setup.barrierEnergy -
              energyInJoules setup.kineticEnergyInsideWell) /
          actionInJouleSeconds setup.reducedPlanckAction ^ 2 ∧
      (∀ x, lengthInMeters setup.wellWidth < x →
        setup.waveFunctionAmplitude x =
          C * Complex.exp (Complex.ofReal
            (waveNumberInInverseMeters κ * x)) +
          D * Complex.exp (Complex.ofReal
            (-waveNumberInInverseMeters κ * x))) ∧
      C = 0 ∧
      Filter.Tendsto setup.waveFunctionAmplitude Filter.atTop (nhds 0) := by
  let L : ℝ := lengthInMeters setup.wellWidth
  let m : ℝ := massInKilograms setup.particleMass
  let U : ℝ := energyInJoules setup.barrierEnergy
  let E : ℝ := energyInJoules setup.kineticEnergyInsideWell
  let h : ℝ := actionInJouleSeconds setup.reducedPlanckAction
  let q : ℝ := 2 * m * (U - E) / h ^ 2
  have hm : 0 < m := _physical.particleMassPositive
  have hUE : 0 < U - E := sub_pos.mpr _physical.kineticEnergyBelowBarrier
  have hh : 0 < h := _physical.reducedPlanckActionPositive
  have hq : 0 < q := by
    dsimp [q]
    positivity
  let k : ℝ := Real.sqrt q
  have hk : 0 < k := Real.sqrt_pos.2 hq
  have hk_sq : k ^ 2 = q := Real.sq_sqrt hq.le
  let κ : WaveNumberQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      (⟨k, hk.le⟩ : WithDim L𝓭⁻¹ NNReal)
  have hκ_readout : waveNumberInInverseMeters κ = k := by
    simp only [waveNumberInInverseMeters, κ,
      CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_self, one_smul]
    rfl
  have hκ_pos : 0 < waveNumberInInverseMeters κ := by
    rw [hκ_readout]
    exact hk
  have hκ_sq :
      waveNumberInInverseMeters κ ^ 2 =
        2 * massInKilograms setup.particleMass *
            (energyInJoules setup.barrierEnergy -
              energyInJoules setup.kineticEnergyInsideWell) /
          actionInJouleSeconds setup.reducedPlanckAction ^ 2 := by
    rw [hκ_readout, hk_sq]
  have hψ_diff :
      DifferentiableOn ℝ setup.waveFunctionAmplitude (Set.Ioi L) := by
    exact _schrodinger.twiceContinuouslyDifferentiableOutside.differentiableOn
      (by norm_num)
  have hψ'_diff :
      DifferentiableOn ℝ (deriv setup.waveFunctionAmplitude) (Set.Ioi L) := by
    exact
      (_schrodinger.twiceContinuouslyDifferentiableOutside.deriv_of_isOpen
        isOpen_Ioi (m := 1) (by norm_num)).differentiableOn_one
  have hODE :
      ∀ x ∈ Set.Ioi L,
        deriv (deriv setup.waveFunctionAmplitude) x =
          (k : ℂ) ^ 2 * setup.waveFunctionAmplitude x := by
    intro x hx
    have heq := _schrodinger.stationaryEquationOutside x hx
    rw [exteriorSchrodingerLeftHandSide] at heq
    change
      Complex.ofReal (-(h ^ 2) / (2 * m)) *
            deriv (deriv setup.waveFunctionAmplitude) x +
          Complex.ofReal U * setup.waveFunctionAmplitude x =
        Complex.ofReal E * setup.waveFunctionAmplitude x at heq
    have hm0 : m ≠ 0 := ne_of_gt hm
    have hh0 : h ≠ 0 := ne_of_gt hh
    have hmc : (m : ℂ) ≠ 0 := by
      exact_mod_cast hm0
    have hhc : (h : ℂ) ≠ 0 := by
      exact_mod_cast hh0
    have hqODE :
        deriv (deriv setup.waveFunctionAmplitude) x =
          Complex.ofReal q * setup.waveFunctionAmplitude x := by
      dsimp [q]
      push_cast [hm0, hh0] at heq ⊢
      field_simp [hmc, hhc] at heq ⊢
      linear_combination -heq
    rw [← hk_sq] at hqODE
    push_cast at hqODE
    exact hqODE
  let fplus : ℝ → ℂ := fun x =>
    Complex.exp (Complex.ofReal (-k * x)) *
      (deriv setup.waveFunctionAmplitude x +
        (k : ℂ) * setup.waveFunctionAmplitude x)
  let fminus : ℝ → ℂ := fun x =>
    Complex.exp (Complex.ofReal (k * x)) *
      (deriv setup.waveFunctionAmplitude x -
        (k : ℂ) * setup.waveFunctionAmplitude x)
  have hFplus_diff : DifferentiableOn ℝ fplus (Set.Ioi L) := by
    intro x hx
    have hψx :=
      (hψ_diff.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
    have hψx' :=
      (hψ'_diff.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
    have he :=
      (((hasDerivAt_id' x).const_mul (-k)).ofReal_comp.cexp)
    exact
      (he.mul (hψx'.add (hψx.const_mul (k : ℂ)))).differentiableAt
        |>.differentiableWithinAt
  have hFminus_diff : DifferentiableOn ℝ fminus (Set.Ioi L) := by
    intro x hx
    have hψx :=
      (hψ_diff.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
    have hψx' :=
      (hψ'_diff.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
    have he :=
      (((hasDerivAt_id' x).const_mul k).ofReal_comp.cexp)
    exact
      (he.mul (hψx'.sub (hψx.const_mul (k : ℂ)))).differentiableAt
        |>.differentiableWithinAt
  have hFplus_deriv : ∀ x ∈ Set.Ioi L, deriv fplus x = 0 := by
    intro x hx
    have hψx :=
      (hψ_diff.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
    have hψx' :=
      (hψ'_diff.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
    have he :=
      (((hasDerivAt_id' x).const_mul (-k)).ofReal_comp.cexp)
    have hd :=
      (he.mul (hψx'.add (hψx.const_mul (k : ℂ)))).deriv
    change deriv fplus x = _ at hd
    rw [hODE x hx] at hd
    rw [hd]
    simp only [Pi.add_apply]
    push_cast
    ring
  have hFminus_deriv : ∀ x ∈ Set.Ioi L, deriv fminus x = 0 := by
    intro x hx
    have hψx :=
      (hψ_diff.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
    have hψx' :=
      (hψ'_diff.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
    have he :=
      (((hasDerivAt_id' x).const_mul k).ofReal_comp.cexp)
    have hd :=
      (he.mul (hψx'.sub (hψx.const_mul (k : ℂ)))).deriv
    change deriv fminus x = _ at hd
    rw [hODE x hx] at hd
    rw [hd]
    simp only [Pi.sub_apply]
    push_cast
    ring
  let x₀ : ℝ := L + 1
  have hx₀ : x₀ ∈ Set.Ioi L := by
    simp [x₀]
  let A : ℂ := fplus x₀
  let B : ℂ := fminus x₀
  have hplus_const : ∀ x ∈ Set.Ioi L, fplus x = A := by
    intro x hx
    exact
      (isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hFplus_diff hFplus_deriv hx hx₀).trans (by rfl)
  have hminus_const : ∀ x ∈ Set.Ioi L, fminus x = B := by
    intro x hx
    exact
      (isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        hFminus_diff hFminus_deriv hx hx₀).trans (by rfl)
  let C : ℂ := A / (2 * (k : ℂ))
  let D : ℂ := -B / (2 * (k : ℂ))
  have hform :
      ∀ x, L < x →
        setup.waveFunctionAmplitude x =
          C * Complex.exp (Complex.ofReal (k * x)) +
          D * Complex.exp (Complex.ofReal (-k * x)) := by
    intro x hx
    have hp := hplus_const x hx
    have hm' := hminus_const x hx
    dsimp [fplus] at hp
    dsimp [fminus] at hm'
    have hkC : (k : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hk
    dsimp [C, D]
    rw [← hp, ← hm']
    push_cast
    have he :
        Complex.exp (-(k : ℂ) * x) *
            Complex.exp ((k : ℂ) * x) =
          1 := by
      rw [← Complex.exp_add]
      simp
    rw [neg_mul] at he
    field_simp [hkC]
    rw [he]
    ring
  let decay : ℝ → ℂ := fun x =>
    Complex.exp (Complex.ofReal (-(k * x)))
  have hkx :
      Filter.Tendsto (fun x : ℝ => k * x) Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos hk).2 Filter.tendsto_id
  have hdecayReal :
      Filter.Tendsto (fun x : ℝ => Real.exp (-(k * x)))
        Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hkx
  have hdecay :
      Filter.Tendsto decay Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [decay, Complex.norm_exp, Complex.ofReal_re] using hdecayReal
  obtain ⟨cutoff, bound, _, _, hbound⟩ :=
    _boundary.eventuallyBoundedAtPositiveInfinity
  have hproduct :
      Filter.Tendsto (fun x => setup.waveFunctionAmplitude x * decay x)
        Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero'
      (g := fun x => bound * Real.exp (-(k * x)))
      (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop cutoff] with x hx
      rw [norm_mul, show ‖decay x‖ = Real.exp (-(k * x)) by
        simp only [decay, Complex.norm_exp, Complex.ofReal_re]]
      exact
        mul_le_mul_of_nonneg_right (hbound x hx) (Real.exp_pos _).le
    · simpa only [mul_zero] using hdecayReal.const_mul bound
  have heq :
      (fun x => setup.waveFunctionAmplitude x * decay x) =ᶠ[Filter.atTop]
        (fun x => C + D * (decay x * decay x)) := by
    filter_upwards [Filter.eventually_gt_atTop L] with x hx
    rw [hform x hx]
    dsimp [decay]
    rw [neg_mul]
    have he :
        Complex.exp (Complex.ofReal (k * x)) *
            Complex.exp (Complex.ofReal (-(k * x))) =
          1 := by
      rw [← Complex.exp_add, ← Complex.ofReal_add]
      simp
    rw [add_mul, mul_assoc, he, mul_one]
    ring
  have hlimit :
      Filter.Tendsto (fun x => C + D * (decay x * decay x))
        Filter.atTop (nhds C) := by
    convert
      tendsto_const_nhds.add
        ((hdecay.mul hdecay).const_mul D) using 1
    all_goals simp
  have hC : C = 0 :=
    (tendsto_nhds_unique_of_eventuallyEq hproduct hlimit heq).symm
  have hψ_limit :
      Filter.Tendsto setup.waveFunctionAmplitude Filter.atTop (nhds 0) := by
    have hEqDecay :
        (fun x => D * decay x) =ᶠ[Filter.atTop]
          setup.waveFunctionAmplitude := by
      filter_upwards [Filter.eventually_gt_atTop L] with x hx
      rw [hform x hx, hC, zero_mul, zero_add]
      simp only [decay, neg_mul]
    apply Filter.Tendsto.congr' hEqDecay
    simpa only [mul_zero] using hdecay.const_mul D
  refine ⟨C, D, κ, hκ_pos, hκ_sq, ?_, hC, hψ_limit⟩
  intro x hx
  rw [hκ_readout]
  exact hform x hx

end PhyXMiniProblems.ProblemPhyXMini0617
