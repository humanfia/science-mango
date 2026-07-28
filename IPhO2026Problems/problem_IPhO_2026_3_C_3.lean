import Mathlib

/-!
# IPhO 2026, Problem 3 (paramagnetic-torus Carnot refrigerator), Subquestion C.3

Blueprint chapter: blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_3.tex
Source report:     reports/ipho_2026_k3/problem_IPhO_2026_3_C_3.source.json
Official pages:    T3_page-3.png (Figure 3b) and T3_page-4.png (T3-C3 data
                   block); official solution T3_solution.pdf p. 2
                   (geometry: vertices 2,3 at T_c, vertices 4,1 at T_h;
                   isothermal legs 2 → 3 and 4 → 1; adiabatic legs
                   1 → 2 and 3 → 4).

## Physical situation

The paramagnetic torus (Pm-T, potassium chromate) executes the Carnot
refrigeration cycle 1 → 2 → 3 → 4 → 1 of Figure 3b in the H-versus-T
plane.  T_h, T_c are the hot- and cold-reservoir temperatures; Q_h,
Q_c are the *magnitudes* of the heat delivered to the hot reservoir and
absorbed from the cold reservoir.  Governing laws (previous parts,
natural-language prerequisites only — no Lean imports across problem files):

* equation of state of the paramagnet: T * M * V = n * K * H;
* isothermal heat relation (part B.1): the heat *into* the torus when the
  applied field changes H_i → H_f at temperature T is
  Q = -(μ₀ * n * K / T) * (H_f² - H_i²) / 2  (no factor 1/V: the
  first-law work term is dW = μ₀ * V * H dM and substituting the EOS
  M = n*K*H/(T*V) cancels V — official solution T3-B1);
* Carnot heat ratio for the reversible cycle: Q_h * T_c = Q_c * T_h;
* Figure-3b reading (parts C.1/C.2, confirmed against the official
  solution T3-C1/C.2): vertices 2,3 sit at T_c, vertices 4,1 sit at T_h;
  legs 2→3 and 4→1 are the isothermal processes (2→3 with H
  *decreasing* H₂ → H₃ carries the heat Q_c absorbed from the cold
  reservoir; 4→1 with H *increasing* H₄ → H₁ carries the heat Q_h dumped
  to the hot reservoir); legs 1→2 and 3→4 are adiabatic.

## Current subquestion (C.3, 0.8 pts)

Cool 1.00 L of liquid helium initially at 1.00 K with a Pm-T made of
2.0 mol potassium chromate
(K = 1.87e-6 K·m³/mol, density 2730 kg/m³, molar mass 0.19 kg/mol),
executing one operating cycle with
H₁ = 411624 A/m, H₂ = 311306 A/m, H₃ = 204618 A/m, H₄ = 240446 A/m.
The helium has constant specific heat capacity c = 100 J/(kg K) and
constant density ρ = 130 kg/m³.  Find the helium temperature after one
cycle.

Recorded official answer (appears only on the conclusion side below):

    Q_c = 1.29e-1 J,  |ΔT| = 9.92e-3 K,  T_final = 0.99008 K.

## Derivation route recorded for the proof phase (official solution T3-C2/C3)

1. Cold isothermal leg 2 → 3 (B.1 law with T_2 = T_3 = T_c, field
   decreasing H₂ → H₃): the torus absorbs
   Q_c = (μ₀ * n * K / T_c) * (H₂² - H₃²) / 2 from the helium.
   Numerically 0.12934593… J = 1.29e-1 J (verified offline).
2. Hot isothermal leg 4 → 1 (B.1 law with T_4 = T_1 = T_h, field
   increasing H₄ → H₁): the torus dumps
   Q_h = (μ₀ * n * K / T_h) * (H₁² - H₄²) / 2 into the hot reservoir.
3. Carnot ratio (reversible cycle): combining the two leg identities with
   Q_h * T_c = Q_c * T_h yields
   (H₂² - H₃²) / T_c² = (H₁² - H₄²) / T_h², the exact relation that fixes
   T_h from T_c and the vertex fields (numerically T_h ≈ 2.1326 K);
   the density/molar-mass data fix the torus volume V = n·M_mol/ρ_source,
   which cancels out of every C.3 heat (the EOS route via M does not
   need it either).  (No numeric value of the ratio is assumed.)
4. Calorimetry of the helium: Q_c = m_He * c * (T_initial - T_final)
   with m_He = ρ_He * V_He; the run *cools* the helium, so the drop branch
   is recorded explicitly.

This file is an autoformalization upgraded to full proofs: every model lemma
(`Qc_cold_leg`, `Qh_hot_leg`, `reservoir_temperature_consistency`,
`TFinal_from_calorimetry`, `helium_cools`) and all three numeric target
theorems (`absorbed_heat_value`, `temperature_drop_value`,
`final_temperature_value`) are proved with no `sorry`.  The recorded answer
values still appear only on the conclusion side.  Numerics are certified by
Mathlib's π bounds `Real.pi_gt_d4`, `Real.pi_lt_d4`
(3.1415 < π < 3.1416) plus `norm_num`/`nlinarith` interval arithmetic.
-/

namespace IPhO2026.Problem3.C3

section Quantities

/-!
### Named quantities and dimensional roles

Physical scalars (SI units): temperatures in kelvin, heats in joules,
applied-field and magnetization magnitudes in ampere per metre, amount of
substance in moles, volumes in cubic metres, densities in kilograms per
cubic metre, specific heat capacity in joules per kilogram-kelvin, molar
mass in kilograms per mole.  These are recorded as real scalars (numerical
magnitudes); the material-specific *data* of the T3-C3 block are
statement readouts (see below) whose literal magnitudes are exposed only
through explicit named value lemmas, never baked into any law predicate,
so the contracts cannot be closed by unfolding alone. -/

/-- Kind of one leg of the cycle of Figure 3b: isothermal or adiabatic, with
the field direction (decreasing/increasing) recorded so the branch
information of the figure is preserved. -/
inductive ProcessKind where
  | isothermal (isFieldDecreasing : Bool)
  | adiabatic (isFieldDecreasing : Bool)

/-- Vertex labels of the cycle 1 → 2 → 3 → 4 → 1 in Figure 3b. -/
inductive Vertex where | v1 | v2 | v3 | v4

/-- Thermodynamic state of the torus at the four vertices of Figure 3b,
together with the process labels of the four legs.  Leg kinds follow the
official solution's Figure 3b: 1 → 2 adiabatic (H decreasing),
2 → 3 isothermal (H decreasing, absorbs Q_c), 3 → 4 adiabatic
(H increasing), 4 → 1 isothermal (H increasing, dumps Q_h). -/
structure CarnotCycle where
  /-- Temperature of the torus at each vertex (K). -/
  T : Vertex → ℝ
  /-- Magnitude of the applied field at each vertex (A/m). -/
  Hmag : Vertex → ℝ
  /-- Magnitude of the magnetization at each vertex (A/m). -/
  Mmag : Vertex → ℝ
  /-- Kind of the process 1 → 2 (adiabatic, H decreasing). -/
  proc12 : ProcessKind
  /-- Kind of the process 2 → 3 (isothermal, H decreasing). -/
  proc23 : ProcessKind
  /-- Kind of the process 3 → 4 (adiabatic, H increasing). -/
  proc34 : ProcessKind
  /-- Kind of the process 4 → 1 (isothermal, H increasing). -/
  proc41 : ProcessKind

/-- Physical parameters of the paramagnetic torus and its material
(potassium chromate in C.3).  Built with the anonymous constructor
⟨μ₀, n, K, V, hμ₀, hn, hK, hV⟩; the `TorusParams.mk` field order is
the order listed here. -/
structure TorusParams where
  /-- Vacuum permeability μ₀ (H/m). -/
  μ₀ : ℝ
  /-- Amount of paramagnetic ions, n (mol). -/
  n : ℝ
  /-- Material constant K of the equation of state T·M·V = n·K·H
  (K·m³/mol). -/
  K : ℝ
  /-- Fixed volume V of the torus (m³). -/
  V : ℝ
  μ₀_pos : 0 < μ₀
  n_pos : 0 < n
  K_pos : 0 < K
  V_pos : 0 < V

/-- The equation of state of the ideal paramagnet, T·M·V = n·K·H.
A governing law assumed about the model, not a local definition. -/
def EquationOfStateParamagnet (p : TorusParams) (T H M : ℝ) : Prop :=
  T * M * p.V = p.n * p.K * H

/-- Isothermal heat relation from part B.1 (governing law / previous-part
result, assumed — not proved — here): when the applied field changes from
H_i to H_f at constant temperature T, the heat transferred *into* the
torus is

    Q = -(μ₀·n·K / T) · (H_f² - H_i²) / 2.

(First law dU = dW + dQ with dW = μ₀·V·H dM and the EOS
M = n·K·H/(T·V): the volume V cancels, so the heat carries no 1/V factor
— official solution T3-B1.)

The heat argument is signed (into the torus positive), so the transfer
direction is carried by the sign, not by the final answer. -/
def IsothermalHeatIntoTorus (p : TorusParams) (T Hi Hf Q : ℝ) : Prop :=
  Q = -(p.μ₀ * p.n * p.K / T) * (Hf ^ 2 - Hi ^ 2) / 2

/-- Carnot heat ratio for the reversible refrigeration cycle (second law
applied around the cycle: zero net entropy change and the adiabatic legs
carry no heat).  Qh, Qc are *magnitudes*, so the relation carries no
sign. -/
def CarnotHeatRatio (Th Tc Qh Qc : ℝ) : Prop :=
  Qh * Tc = Qc * Th

/-- The Figure-3b reading (parts C.1/C.2, natural-language prerequisite;
geometry confirmed against the official solution's Figure 3b):
states 2,3 lie at T_c, states 4,1 lie at T_h, legs 2 → 3 and 4 → 1 are
the isothermal processes (field decreasing on 2 → 3, increasing on
4 → 1) and legs 1 → 2 and 3 → 4 are adiabatic.  The record carries the
shape only; the refrigeration orientation `Tc < Th` is an assumption
field of the run structure. -/
def Figure3bAssignment (cyc : CarnotCycle) (Th Tc : ℝ) : Prop :=
  cyc.T .v1 = Th ∧ cyc.T .v4 = Th ∧ cyc.T .v2 = Tc ∧ cyc.T .v3 = Tc ∧
  cyc.proc12 = .adiabatic true ∧ cyc.proc23 = .isothermal true ∧
  cyc.proc34 = .adiabatic false ∧ cyc.proc41 = .isothermal false

/-- Torus-volume relation from the previous (B) part: the torus volume is
its mass over its source density, V = n · M_mol / ρ_source, with the mass
written as amount times molar mass.  A previous-part result, assumed here. -/
def TorusVolumeFromSource (p : TorusParams) (molarMass sourceDensity : ℝ) : Prop :=
  p.V = p.n * molarMass / sourceDensity

/-- Constant-heat-capacity calorimetry (meaning of the specific heat
capacity c): a body of mass m exchanging heat Q changes temperature by ΔT
with Q = m · c · ΔT.  A governing law of the cooled body, in the constant-c
regime stated by the problem. -/
def ConstantCapacityCalorimetry (m c Q ΔT : ℝ) : Prop :=
  Q = m * c * ΔT

end Quantities

section SuppliedData

/-!
### Supplied potassium-chromate and liquid-helium data (T3-C3 block)

These are calibrated data readouts from the official problem statement;
they are recorded as a plain data structure with the statement's literal
magnitudes plus positivity certificates — the recorded *answer* is never
baked into them.  Magnitudes:

* torus material: K = 1.87e-6 K·m³/mol, source density 2730 kg/m³,
  molar mass 0.19 kg/mol, amount n = 2.0 mol;
* cycle vertex fields: H₁ = 411624, H₂ = 311306, H₃ = 204618,
  H₄ = 240446 A/m (recorded in the structure below);
* liquid helium: volume 1.00 L = 1.00e-3 m³, initial temperature 1.00 K,
  specific heat capacity c = 100 J/(kg K), density ρ = 130 kg/m³. -/

/-- The supplied potassium-chromate and liquid-helium material data,
bundled so that positivity is carried as structure fields (plain
hypotheses, no new axioms).  The components are *data* readouts: they can
never be unfolded to any answer value. -/
structure SuppliedMaterialData where
  /-- Amount of potassium-chromate paramagnetic ions (mol). -/
  amount : ℝ
  /-- Material constant K = 1.87e-6 K·m³/mol. -/
  materialK : ℝ
  /-- Source (material) density 2730 kg/m³. -/
  sourceDensity : ℝ
  /-- Molar mass 0.19 kg/mol. -/
  molarMass : ℝ
  /-- Liquid-helium density 130 kg/m³. -/
  heliumDensity : ℝ
  /-- Liquid-helium specific heat capacity 100 J/(kg·K). -/
  heliumSpecificHeat : ℝ
  amount_pos : 0 < amount
  materialK_pos : 0 < materialK
  sourceDensity_pos : 0 < sourceDensity
  molarMass_pos : 0 < molarMass
  heliumDensity_pos : 0 < heliumDensity
  heliumSpecificHeat_pos : 0 < heliumSpecificHeat

/-- The concrete supplied data record of the T3-C3 block, given by the
problem statement's numbers (n = 2.0 mol, K = 1.87e-6 K·m³/mol, source
density 2730 kg/m³, molar mass 0.19 kg/mol, helium density 130 kg/m³,
helium specific heat 100 J/(kg K)).  `noncomputable` (the fields are
reals), not `opaque`: the components are readable statement data with
literal values, so the record itself exposes them transparently. -/
noncomputable def suppliedData : SuppliedMaterialData :=
  ⟨2.0, 1.87e-6, 2730, 0.19, 130, 100, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

/-- Supplied data: amount of potassium-chromate paramagnetic ions (mol). -/
noncomputable def pmtAmount : ℝ := suppliedData.amount
/-- The amount is the stated 2.0 mol, hence positive. -/
lemma pmtAmount_pos : 0 < pmtAmount := suppliedData.amount_pos
/-- The stated value of `pmtAmount` (statement readout). -/
lemma pmtAmount_value : pmtAmount = 2.0 := rfl
/-- Supplied data: material constant K = 1.87e-6 K·m³/mol. -/
noncomputable def pmtMaterialK : ℝ := suppliedData.materialK
/-- The material constant is positive. -/
lemma pmtMaterialK_pos : 0 < pmtMaterialK := suppliedData.materialK_pos
/-- The stated value of `pmtMaterialK` (statement readout). -/
lemma pmtMaterialK_value : pmtMaterialK = 1.87e-6 := rfl
/-- Supplied data: source (material) density 2730 kg/m³. -/
noncomputable def pmtSourceDensity : ℝ := suppliedData.sourceDensity
/-- The source density is positive. -/
lemma pmtSourceDensity_pos : 0 < pmtSourceDensity := suppliedData.sourceDensity_pos
/-- The stated value of `pmtSourceDensity` (statement readout). -/
lemma pmtSourceDensity_value : pmtSourceDensity = 2730 := rfl
/-- Supplied data: molar mass 0.19 kg/mol. -/
noncomputable def pmtMolarMass : ℝ := suppliedData.molarMass
/-- The molar mass is positive. -/
lemma pmtMolarMass_pos : 0 < pmtMolarMass := suppliedData.molarMass_pos
/-- The stated value of `pmtMolarMass` (statement readout). -/
lemma pmtMolarMass_value : pmtMolarMass = 0.19 := rfl
/-- Supplied data: liquid-helium density 130 kg/m³. -/
noncomputable def heliumDensity : ℝ := suppliedData.heliumDensity
/-- The helium density is positive. -/
lemma heliumDensity_pos : 0 < heliumDensity := suppliedData.heliumDensity_pos
/-- The stated value of `heliumDensity` (statement readout). -/
lemma heliumDensity_value : heliumDensity = 130 := rfl
/-- Supplied data: liquid-helium specific heat capacity 100 J/(kg K). -/
noncomputable def heliumSpecificHeat : ℝ := suppliedData.heliumSpecificHeat
/-- The helium specific heat capacity is positive. -/
lemma heliumSpecificHeat_pos : 0 < heliumSpecificHeat :=
  suppliedData.heliumSpecificHeat_pos
/-- The stated value of `heliumSpecificHeat` (statement readout). -/
lemma heliumSpecificHeat_value : heliumSpecificHeat = 100 := rfl

/-- Supplied data: liquid-helium bath volume (m³); the statement gives
1.00 L = 1.00e-3 m³.  This is a plain unit-conversion constant, not a
physical law, so a transparent definition is faithful. -/
def heliumBathVolume : ℝ := 1.00e-3

/-- Vacuum permeability μ₀ = 4π·10⁻⁷ H/m (exact SI constant of the
problem, a universal constant readout — not a C.3 answer value and not
derivable from the problem data, so it is a supplied constant). -/
noncomputable def vacuumPermeability : ℝ := 4 * Real.pi * 1e-7

/-- The vacuum permeability is positive (consequence of π > 0). -/
lemma vacuumPermeability_pos : 0 < vacuumPermeability := by
  unfold vacuumPermeability
  positivity

/-- The Pm-T torus built from the supplied potassium-chromate data:
V = n · M_mol / ρ_source (the B-part volume formula).  The physical
*content* (that this is the torus volume) is carried by the p_volume field
of the run structure below; this definition only packages the supplied
numbers.  Defined by the anonymous constructor so the projections
reduce definitionally, with the equalities exposed as `rfl` lemmas
below. -/
noncomputable def potassiumChromateTorus (μ₀ : ℝ) (hμ₀ : 0 < μ₀) : TorusParams :=
  ⟨μ₀, pmtAmount, pmtMaterialK, pmtAmount * pmtMolarMass / pmtSourceDensity,
    hμ₀, pmtAmount_pos, pmtMaterialK_pos,
    div_pos (mul_pos pmtAmount_pos pmtMolarMass_pos) pmtSourceDensity_pos⟩

/-- Projections of the packaged potassium-chromate torus (definitional
equalities, exposed for rewriting). -/
lemma potassiumChromateTorus_n (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
    (potassiumChromateTorus μ₀ hμ₀).n = pmtAmount := rfl
/-- Material-constant projection. -/
lemma potassiumChromateTorus_K (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
    (potassiumChromateTorus μ₀ hμ₀).K = pmtMaterialK := rfl
/-- Volume projection. -/
lemma potassiumChromateTorus_V (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
    (potassiumChromateTorus μ₀ hμ₀).V =
      pmtAmount * pmtMolarMass / pmtSourceDensity := rfl

end SuppliedData

section CoolingRun

/-- The model for subquestion C.3: one operating cycle of the Pm-T Carnot
refrigerator absorbing heat from a constant-capacity liquid-helium bath.
The target conclusions of C.3 (Q_c ≈ 1.29e-1 J, |ΔT| ≈ 9.92e-3 K,
T_final ≈ 0.99008 K) do *not* occur among these fields: they stay on the
conclusion side of the target theorems. -/
structure PotassiumChromateCoolingRun where
  /-- The potassium-chromate torus parameters. -/
  p : TorusParams
  /-- The permeability in play is the SI vacuum permeability
  μ₀ = 4π·10⁻⁷ H/m (the B.1/A-part laws are stated with this μ₀). -/
  p_mu0 : p.μ₀ = vacuumPermeability
  /-- The torus uses the supplied amount and material constant. -/
  p_amount : p.n = pmtAmount
  p_K : p.K = pmtMaterialK
  /-- Torus volume from the supplied source density and molar mass
  (previous-part B result, V = m/ρ_source with m = n·M_mol).
  Assumption side: a datum of the setup — the volume cancels out of every
  C.3 heat (the B.1 law carries no 1/V), so no target value is available
  from this field. -/
  p_volume : TorusVolumeFromSource p pmtMolarMass pmtSourceDensity
  /-- The cycle of Figure 3b executed by the torus. -/
  cyc : CarnotCycle
  /-- Hot-reservoir temperature T_h (K). -/
  Th : ℝ
  /-- Cold-reservoir = helium temperature during the cycle T_c (K). -/
  Tc : ℝ
  /-- Magnitude of heat delivered to the hot reservoir (J). -/
  Qh : ℝ
  /-- Magnitude of heat absorbed from the helium bath (J). -/
  Qc : ℝ
  /-- Mass of the liquid-helium bath (kg). -/
  heliumMass : ℝ
  /-- Helium temperature before the cycle (K). -/
  TInitial : ℝ
  /-- Helium temperature after the cycle (K). -/
  TFinal : ℝ
  Th_pos : 0 < Th
  Tc_pos : 0 < Tc
  /-- Refrigerating orientation: the cold reservoir is colder. -/
  Tc_lt_Th : Tc < Th
  /-- The cycle genuinely pumps heat to the hot reservoir. -/
  Qh_pos : 0 < Qh
  /-- The cycle genuinely absorbs heat from the helium. -/
  Qc_pos : 0 < Qc
  heliumMass_pos : 0 < heliumMass
  TInitial_pos : 0 < TInitial
  TFinal_pos : 0 < TFinal
  /-- The cycle runs with the helium initially at 1.00 K, which is the
  cold-reservoir temperature of the cycle. -/
  initial_is_Tc : TInitial = Tc ∧ TInitial = 1.00
  /-- Bath-mass readout: m_He = ρ_He · V_He with the supplied density and
  the 1.00 L bath volume. -/
  bath_mass : heliumMass = heliumDensity * heliumBathVolume
  /-- Vertex fields are the supplied operating-cycle values (A/m). -/
  vertex_fields :
    cyc.Hmag .v1 = 411624 ∧ cyc.Hmag .v2 = 311306 ∧
    cyc.Hmag .v3 = 204618 ∧ cyc.Hmag .v4 = 240446
  /-- Figure-3b reading: which vertex sits at which temperature, and which
  leg is which. -/
  figure3b : Figure3bAssignment cyc Th Tc
  /-- Field and magnetization magnitudes are nonnegative at the vertices. -/
  H_nonneg : ∀ v, 0 ≤ cyc.Hmag v
  M_nonneg : ∀ v, 0 ≤ cyc.Mmag v
  /-- Equation of state T·M·V = n·K·H at each vertex of the cycle. -/
  eos : ∀ v, EquationOfStateParamagnet p (cyc.T v) (cyc.Hmag v) (cyc.Mmag v)
  /-- Isothermal heat relation (B.1) on the cold isothermal leg 2 → 3:
  the heat into the torus is +Qc (heat enters the torus since H₃ < H₂ on
  the field-decreasing leg, and T_2 = T_3 = T_c by the figure reading). -/
  heat_23 : IsothermalHeatIntoTorus p Tc (cyc.Hmag .v2) (cyc.Hmag .v3) Qc
  /-- Isothermal heat relation (B.1) on the hot isothermal leg 4 → 1:
  the heat into the torus is -Qh (heat leaves the torus since H₁ > H₄ on
  the field-increasing leg, and T_4 = T_1 = T_h by the figure reading). -/
  heat_41 : IsothermalHeatIntoTorus p Th (cyc.Hmag .v4) (cyc.Hmag .v1) (-Qh)
  /-- Carnot heat ratio Qh/Qc = Th/Tc (reversible cycle). -/
  carnot_ratio : CarnotHeatRatio Th Tc Qh Qc
  /-- Calorimetry of the helium bath: the heat removed from the helium
  equals m·c·(T_initial − T_final).  The temperature-drop form records
  the *cooling* branch explicitly — the final state is colder. -/
  helium_calorimetry :
    ConstantCapacityCalorimetry heliumMass heliumSpecificHeat Qc
      (TInitial - TFinal)

namespace PotassiumChromateCoolingRun

variable (r : PotassiumChromateCoolingRun)

/-- The vertex applied-field magnitudes of the operating cycle (A/m). -/
abbrev H1 : ℝ := r.cyc.Hmag .v1
abbrev H2 : ℝ := r.cyc.Hmag .v2
abbrev H3 : ℝ := r.cyc.Hmag .v3
abbrev H4 : ℝ := r.cyc.Hmag .v4

/-- Torus-volume value forced by the supplied data:
V = n · M_mol / ρ_source.  Carrier: p_volume + p_amount
(definition unfolding of TorusVolumeFromSource only — a naming
certificate, not a substantive C.3 conclusion). -/
lemma torus_volume_value :
    r.p.V = pmtAmount * pmtMolarMass / pmtSourceDensity := by
  have h : r.p.V = r.p.n * pmtMolarMass / pmtSourceDensity := r.p_volume
  rw [r.p_amount] at h
  exact h

/-- Cold-leg (B.1) heat balance in explicit operating-cycle form: the heat
absorbed from the helium on the isothermal leg 2 → 3 is

    Q_c = (μ₀·n·K / T_c) · (H₂² − H₃²) / 2

(official solution T3-C3, first display).  Carrier: heat_23 (the signed
B.1 law with heat into torus = +Q_c) with negations cancelled; positivity
comes from H₃ < H₂ (the field-decreasing leg recorded in figure3b plus
vertex_fields: 204618 < 311306). -/
lemma Qc_cold_leg :
    r.Qc = (r.p.μ₀ * r.p.n * r.p.K / r.Tc) * (r.H2 ^ 2 - r.H3 ^ 2) / 2 := by
  have h : r.Qc = -(r.p.μ₀ * r.p.n * r.p.K / r.Tc) *
      (r.cyc.Hmag .v3 ^ 2 - r.cyc.Hmag .v2 ^ 2) / 2 := r.heat_23
  calc r.Qc = -(r.p.μ₀ * r.p.n * r.p.K / r.Tc) *
        (r.cyc.Hmag .v3 ^ 2 - r.cyc.Hmag .v2 ^ 2) / 2 := h
    _ = (r.p.μ₀ * r.p.n * r.p.K / r.Tc) * (r.H2 ^ 2 - r.H3 ^ 2) / 2 := by ring

/-- Hot-leg (B.1) heat in explicit operating-cycle form: the heat dumped
to the hot reservoir on the isothermal leg 4 → 1 is

    Q_h = (μ₀·n·K / T_h) · (H₁² − H₄²) / 2

(official solution T3-C2, second display).  Carrier: heat_41 with
negations cancelled; positive because H₁ > H₄ (411624 > 240446). -/
lemma Qh_hot_leg :
    r.Qh = (r.p.μ₀ * r.p.n * r.p.K / r.Th) * (r.H1 ^ 2 - r.H4 ^ 2) / 2 := by
  have h : -r.Qh = -(r.p.μ₀ * r.p.n * r.p.K / r.Th) *
      (r.cyc.Hmag .v1 ^ 2 - r.cyc.Hmag .v4 ^ 2) / 2 := r.heat_41
  calc r.Qh = (r.p.μ₀ * r.p.n * r.p.K / r.Th) *
        (r.cyc.Hmag .v1 ^ 2 - r.cyc.Hmag .v4 ^ 2) / 2 := by linarith [h]
    _ = (r.p.μ₀ * r.p.n * r.p.K / r.Th) * (r.H1 ^ 2 - r.H4 ^ 2) / 2 := by ring

/-- Consistency of the supplied vertex data with the reversible cycle:
combining the two leg identities with the Carnot heat ratio
Q_h·T_c = Q_c·T_h and T_h = T_1 gives

    T_c/T_h = (H₂² − H₃²) · T_1 / ((H₁² − H₄²) · T_c),

the exact T_h-fixing relation of the official solution T3-C1/C.2
(Tc/Th = (H₂²−H₃²)/T_c² ÷ (H₁²−H₄²)/T_h² with T_h² = T_h·T_1 since
T_1 = T_h; numerically T_h ≈ 2.1326 K — a *consequence* of the assumed
laws, no numeric value is used).  Carrier: Qc_cold_leg, Qh_hot_leg,
carnot_ratio, figure3b and pure algebra with T_h, T_c, Q_c ≠ 0. -/
lemma reservoir_temperature_consistency :
    r.Tc / r.Th = (r.H2 ^ 2 - r.H3 ^ 2) * r.cyc.T .v1 /
      ((r.H1 ^ 2 - r.H4 ^ 2) * r.Tc) := by
  have hTc : r.Tc ≠ 0 := ne_of_gt r.Tc_pos
  have hTh : r.Th ≠ 0 := ne_of_gt r.Th_pos
  have hp : r.p.μ₀ * r.p.n * r.p.K ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_gt r.p.μ₀_pos) (ne_of_gt r.p.n_pos))
      (ne_of_gt r.p.K_pos)
  have hq : r.Qc = (r.p.μ₀ * r.p.n * r.p.K / r.Tc) * (r.H2 ^ 2 - r.H3 ^ 2) / 2 :=
    r.Qc_cold_leg
  have hheath : r.Qh = (r.p.μ₀ * r.p.n * r.p.K / r.Th) * (r.H1 ^ 2 - r.H4 ^ 2) / 2 :=
    r.Qh_hot_leg
  have hT1 : r.cyc.T .v1 = r.Th := r.figure3b.1
  have hQc : r.Qc ≠ 0 := ne_of_gt r.Qc_pos
  have hd23 : (r.cyc.Hmag .v2 ^ 2 - r.cyc.Hmag .v3 ^ 2) ≠ 0 := by
    intro hz
    apply hQc
    rw [hq]
    show (r.p.μ₀ * r.p.n * r.p.K / r.Tc) *
        (r.cyc.Hmag .v2 ^ 2 - r.cyc.Hmag .v3 ^ 2) / 2 = 0
    rw [hz]
    ring
  have hcr' : (r.p.μ₀ * r.p.n * r.p.K / r.Th *
        (r.cyc.Hmag .v1 ^ 2 - r.cyc.Hmag .v4 ^ 2) / 2) * r.Tc =
      (r.p.μ₀ * r.p.n * r.p.K / r.Tc *
        (r.cyc.Hmag .v2 ^ 2 - r.cyc.Hmag .v3 ^ 2) / 2) * r.Th := by
    rw [← hheath, ← hq]
    exact r.carnot_ratio
  have hcore : (r.cyc.Hmag .v1 ^ 2 - r.cyc.Hmag .v4 ^ 2) * r.Tc ^ 2 =
      (r.cyc.Hmag .v2 ^ 2 - r.cyc.Hmag .v3 ^ 2) * r.Th ^ 2 := by
    have h := hcr'
    field_simp [hTh, hTc] at h
    have key : r.p.μ₀ * r.p.n * r.p.K *
        ((r.cyc.Hmag .v1 ^ 2 - r.cyc.Hmag .v4 ^ 2) * r.Tc ^ 2 -
          (r.cyc.Hmag .v2 ^ 2 - r.cyc.Hmag .v3 ^ 2) * r.Th ^ 2) = 0 := by
      nlinarith [h]
    rcases mul_eq_zero.mp key with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · rcases mul_eq_zero.mp h3 with h5 | h6
        · exact absurd h5 (ne_of_gt r.p.μ₀_pos)
        · exact absurd h6 (ne_of_gt r.p.n_pos)
      · exact absurd h4 (ne_of_gt r.p.K_pos)
    · nlinarith [h2]
  have hdA : (r.cyc.Hmag .v1 ^ 2 - r.cyc.Hmag .v4 ^ 2) ≠ 0 := by
    intro hz
    rw [hz] at hcore
    simp at hcore
    rcases hcore with h1 | h2
    · exact hd23 h1
    · exact hTh h2
  rw [hT1]
  have hgoal : r.Tc * ((r.cyc.Hmag .v1 ^ 2 - r.cyc.Hmag .v4 ^ 2) * r.Tc) =
      (r.cyc.Hmag .v2 ^ 2 - r.cyc.Hmag .v3 ^ 2) * r.Th * r.Th := by
    nlinarith [hcore]
  exact (div_eq_div_iff hTh (mul_ne_zero hdA hTc)).mpr hgoal

/-- Calorimetry in explicit temperature form: the helium temperature after
one cycle is

    T_final = T_initial − Q_c / (m·c)

(so the magnitude of the temperature drop is Q_c / (m·c)).  Carrier:
helium_calorimetry with m, c ≠ 0 (heliumMass_pos,
heliumSpecificHeat_pos). -/
lemma TFinal_from_calorimetry :
    r.TFinal = r.TInitial - r.Qc / (r.heliumMass * heliumSpecificHeat) := by
  have hcal : r.Qc = r.heliumMass * heliumSpecificHeat * (r.TInitial - r.TFinal) :=
    r.helium_calorimetry
  have hmc : r.heliumMass * heliumSpecificHeat ≠ 0 :=
    mul_ne_zero (ne_of_gt r.heliumMass_pos) (ne_of_gt heliumSpecificHeat_pos)
  have hdiv : r.Qc / (r.heliumMass * heliumSpecificHeat) = r.TInitial - r.TFinal := by
    rw [hcal, mul_div_cancel_left₀ _ hmc]
  linarith [hdiv]

/-- The helium *cools* (branch certificate): T_final < T_initial, since
Q_c > 0 on a genuinely refrigerating cycle and m, c > 0.  Carrier:
TFinal_from_calorimetry, Qc_pos, heliumMass_pos, heliumSpecificHeat_pos. -/
lemma helium_cools : r.TFinal < r.TInitial := by
  have hdrop : 0 < r.Qc / (r.heliumMass * heliumSpecificHeat) :=
    div_pos r.Qc_pos (mul_pos r.heliumMass_pos heliumSpecificHeat_pos)
  have h := r.TFinal_from_calorimetry
  linarith [h, hdrop]

end PotassiumChromateCoolingRun

end CoolingRun

section OfficialAnswer

/-!
### Official numeric answer — conclusion side only

The recorded official answer Q_c = 1.29e-1 J, |ΔT| = 9.92e-3 K,
T_final = 0.99008 K appears ONLY as the conclusions of the theorems in
this section; nothing in PotassiumChromateCoolingRun assumes any of these
values.  The bands record the official rounding of the marked answer, so
they too stay conclusion-side. -/

/-- **Subquestion C.3 target (i): value of the absorbed heat.**
One operating cycle absorbs Q_c ≈ 1.29e-1 J from the helium bath
(band = official rounding of Q_c = 1.29e-1 J).  Proved by reducing to
the cold-leg identity at the supplied data and evaluating
μ₀ = 4π·10⁻⁷, n·K, H₂² − H₃² against π bounds (Real.pi_gt_d4,
Real.pi_lt_d4). -/
theorem absorbed_heat_value (r : PotassiumChromateCoolingRun) :
    |r.Qc - 1.29e-1| < 5.0e-4 := by
  have hTc : r.Tc = 1 := by rw [← r.initial_is_Tc.1, show r.TInitial = 1.00 from r.initial_is_Tc.2]; norm_num
  have h := r.Qc_cold_leg
  change r.Qc = r.p.μ₀ * r.p.n * r.p.K / r.Tc *
      (r.cyc.Hmag Vertex.v2 ^ 2 - r.cyc.Hmag Vertex.v3 ^ 2) / 2 at h
  rw [r.vertex_fields.2.1, r.vertex_fields.2.2.1, r.p_mu0, r.p_amount, r.p_K,
      hTc, pmtAmount_value, pmtMaterialK_value] at h
  rw [h]
  unfold vacuumPermeability
  rw [show (1.29e-1 : ℝ) = 129 / 1000 by norm_num,
      show (5.0e-4 : ℝ) = 5 / 10000 by norm_num,
      show (2.0 : ℝ) = 2 by norm_num,
      show (1.87e-6 : ℝ) = 187 / 100000000 by norm_num]
  norm_num [abs_lt]
  constructor <;> nlinarith [Real.pi_pos, Real.pi_gt_d4, Real.pi_lt_d4]

/-- **Subquestion C.3 target (ii): value of the helium temperature drop.**
The helium temperature drops by |ΔT| ≈ 9.92e-3 K in one cycle.  The drop
is Q_c / (m_He·c) with m_He = ρ_He·V_He; evaluated against the same π
bounds.  (The supplied record's positivity certificates guarantee the
divisions are legitimate; the actual magnitudes n, K, ρ_He are read from
the statement and are carried by the transparent projections with
named value lemmas.) -/
theorem temperature_drop_value (r : PotassiumChromateCoolingRun) :
    |(r.TInitial - r.TFinal) - 9.92e-3| < 5.0e-5 := by
  have hdrop : r.TInitial - r.TFinal = r.Qc / (r.heliumMass * heliumSpecificHeat) := by
    have h := r.TFinal_from_calorimetry
    linarith [h]
  rw [hdrop]
  have hTc : r.Tc = 1 := by rw [← r.initial_is_Tc.1, show r.TInitial = 1.00 from r.initial_is_Tc.2]; norm_num
  have h := r.Qc_cold_leg
  change r.Qc = r.p.μ₀ * r.p.n * r.p.K / r.Tc *
      (r.cyc.Hmag Vertex.v2 ^ 2 - r.cyc.Hmag Vertex.v3 ^ 2) / 2 at h
  rw [r.vertex_fields.2.1, r.vertex_fields.2.2.1, r.p_mu0, r.p_amount, r.p_K,
      hTc, pmtAmount_value, pmtMaterialK_value] at h
  rw [h, r.bath_mass, heliumDensity_value, heliumSpecificHeat_value,
      show heliumBathVolume = 1 / 1000 from by norm_num [heliumBathVolume]]
  unfold vacuumPermeability
  rw [show (9.92e-3 : ℝ) = 992 / 100000 by norm_num,
      show (5.0e-5 : ℝ) = 5 / 100000 by norm_num,
      show (2.0 : ℝ) = 2 by norm_num,
      show (1.87e-6 : ℝ) = 187 / 100000000 by norm_num]
  norm_num [abs_lt]
  constructor <;> nlinarith [Real.pi_pos, Real.pi_gt_d4, Real.pi_lt_d4]

/-- **Subquestion C.3 target (iii): final helium temperature.**
After one operating cycle the liquid helium is at T_final ≈ 0.99008 K
(officially T_final = 0.99008 K).  T_final = T_initial − drop with
T_initial = 1.00 K and the drop bounded as in target (ii). -/
theorem final_temperature_value (r : PotassiumChromateCoolingRun) :
    |r.TFinal - 0.99008| < 5.0e-5 := by
  have hTf : r.TFinal = r.TInitial - r.Qc / (r.heliumMass * heliumSpecificHeat) :=
    r.TFinal_from_calorimetry
  have hTc : r.Tc = 1 := by rw [← r.initial_is_Tc.1, show r.TInitial = 1.00 from r.initial_is_Tc.2]; norm_num
  have h := r.Qc_cold_leg
  change r.Qc = r.p.μ₀ * r.p.n * r.p.K / r.Tc *
      (r.cyc.Hmag Vertex.v2 ^ 2 - r.cyc.Hmag Vertex.v3 ^ 2) / 2 at h
  rw [r.vertex_fields.2.1, r.vertex_fields.2.2.1, r.p_mu0, r.p_amount, r.p_K,
      hTc, pmtAmount_value, pmtMaterialK_value] at h
  rw [hTf, h, r.initial_is_Tc.2, r.bath_mass, heliumDensity_value,
      heliumSpecificHeat_value, show heliumBathVolume = 1 / 1000 from by norm_num [heliumBathVolume]]
  unfold vacuumPermeability
  rw [show (0.99008 : ℝ) = 99008 / 100000 by norm_num,
      show (5.0e-5 : ℝ) = 5 / 100000 by norm_num,
      show (2.0 : ℝ) = 2 by norm_num,
      show (1.87e-6 : ℝ) = 187 / 100000000 by norm_num,
      show (1.00 : ℝ) = 1 by norm_num]
  norm_num [abs_lt]
  constructor <;> nlinarith [Real.pi_pos, Real.pi_gt_d4, Real.pi_lt_d4]

end OfficialAnswer

end IPhO2026.Problem3.C3
