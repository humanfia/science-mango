import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Theory Problem T8, part 8.6 — quantum yield for CO formation

Source: 58th International Chemistry Olympiad, Tashkent 2026, theory problem
T8 ("Recycling of Carbon Dioxide"), subquestion 8.6 (10 pt), problem PDF p. 73,
image `T8_page-2.png`; marking scheme on solution PDF p. 74.

## Source contract

Given (shared context of 8.5–8.6, printed on `T8_page-2.png`):

* the supported catalyst is **1** loaded on crystalline carbon nitride C₃N₄;
* catalyst mass fraction `ω_cat = 3.8%`, defined (8.5) by
  `ω_cat = m_cat / (m_cat + m_C3N4) · 100%`;
* catalyst molar mass `M_cat = 557.21 g mol⁻¹`;
* the sample under illumination is `10 mg` of C₃N₄ loaded with **1**;
* turnover frequency `TOF = 8 h⁻¹`, defined as product molecules formed per
  active catalyst molecule per hour;
* LED illumination: wavelength `λ = 390 nm`, power `P = 50 mW`;
* quantum yield definition (printed in the paper):
  `φ = (number of reacted electrons) / (number of incident photons) · 100%`;
* from 8.1 (half equation for CO₂ reduction in acidic medium,
  `CO₂ + 2H⁺ + 2e⁻ → CO + H₂O`), each CO formed consumes `z = 2` electrons.

Physical constants used by the marking scheme (printed in its computation):
Avogadro constant `N_A = 6.02e23 mol⁻¹`, and `E_photon = h·c/λ = 5.1e-19 J`
corresponding to `h = 6.626e-34 J s` and `c = 3.00e8 m s⁻¹`.

Requested conclusion: the quantum yield `φ` (%) for CO formation.

## Recorded marking-scheme computation

`m_cat = 3.95e-4 g`, `n_cat = 7.089e-7 mol`,
`r_CO = n_cat · TOF · N_A / 3600 = 9.48e14 s⁻¹`,
`E_photon = h·c/λ = 5.1e-19 J`, `r_photon = P/E_photon = 9.8e16 s⁻¹`,
and (eq. 8.6.1) `φ = r_CO · 2 / r_photon · 100% = 1.94%`.

Exact evaluation of the stated data with the marking-scheme constants gives
`φ_raw = 1.9334888…%`, and the rubric's own printed intermediate values give
`φ_printed = 9.48e14 · 2 / 9.8e16 · 100% = 474/245 % = 1.9346939…%`.  Both
values round to `1.93%` by the standard nearest-two-decimal rule:
`|φ_raw − 1.93| = 0.00349 < 0.005` and `|φ_printed − 1.93| = 0.00469 < 0.005`.

**Source inconsistency (recorded in prose only).** The official rubric prints
`φ = 1.94%`.  That figure is *not* the standard two-decimal rounding of the
computed value: `|φ_raw − 1.94| = 0.00651 > 0.005`, and even the rubric's own
printed intermediates give `|474/245 − 1.94| = 0.00531 > 0.005`.  The value
`1.94%` is therefore recorded here only as the official rubric-reported value;
no theorem in this file claims that `φ` equals or rounds to `1.94%`, no
post-hoc `|φ − 1.94| ≤ 0.01` bound is used as a rounding claim, and no
staged-rounding argument is invented to justify the rubric figure.

The main theorem is stated honestly as `|φ − 1.93| < 0.005` (percentage
points), i.e. the computed quantum yield rounds to `1.93%` at two decimals; a
companion theorem pins the raw value by `|φ − 1.9335| < 5e-5`, and a second
companion evaluates eq. 8.6.1 at the rubric's rounded checkpoints, obtaining
exactly `474/245 %`, which likewise rounds to `1.93%`.  Each rubric checkpoint
(`r_CO`, `E_photon`, `r_photon`) is stated as a bound at its printed last
digit; all three bounds were verified to hold (actual deviations
`3.6e11`, `3.1e-22` and `9.9e13` against tolerances `1e12`, `1e-21` and
`1e14`).

## Modeling conventions

Following `IChO2026Chem`, every quantity is a real numerical readout in its
source unit: masses in g, molar mass in g mol⁻¹, TOF in h⁻¹, wavelength in m,
power in W, energies in J, rates in s⁻¹, `ω_cat` and `φ` on the percent scale.
Physlib exposes the Planck constant only as `Constants.ℏ` (with `h = 2πℏ`) and
the speed of light only in dimension-carrying form, and no Avogadro constant;
the three constants are therefore carried as explicit hypotheses with the
marking scheme's values, so no empirical datum is smuggled into a definition.
-/

namespace IChO2026T8A6

/-- Catalyst mass fraction on the percent scale, the loading relation of 8.5:
`ω_cat = m_cat / (m_cat + m_support) · 100%`. -/
noncomputable def massFractionPercent (catalystMass supportMass : ℝ) : ℝ :=
  catalystMass / (catalystMass + supportMass) * 100

/-- Number of catalyst molecules in the loaded sample:
`N_cat = (m_cat / M_cat) · N_A`. -/
noncomputable def catalystMolecules (avogadro catalystMass molarMassCat : ℝ) : ℝ :=
  catalystMass / molarMassCat * avogadro

/-- CO formation rate in molecules `s⁻¹` from the turnover frequency:
`r_CO = TOF · N_cat / 3600` (TOF counts product molecules per active catalyst
molecule per hour, and there are 3600 s in one hour). -/
noncomputable def coFormationRate (tof catalystMoleculeCount : ℝ) : ℝ :=
  tof * catalystMoleculeCount / 3600

/-- Photon energy `E = h·c/λ` in joule, with `h` in J s, `c` in m `s⁻¹` and
`λ` in m. -/
noncomputable def photonEnergy (planckConstant speedOfLight wavelength : ℝ) : ℝ :=
  planckConstant * speedOfLight / wavelength

/-- Incident photon rate `r_photon = P / E_photon` in photons `s⁻¹`, with
illumination power `P` in watt. -/
noncomputable def incidentPhotonRate (power photonEnergyValue : ℝ) : ℝ :=
  power / photonEnergyValue

/-- Quantum yield on the percent scale, equation 8.6.1 of the marking scheme:
`φ = z · r_CO / r_photon · 100%`, where `z` is the number of electrons reacted
per CO molecule formed (`z = 2` by the 8.1 half equation) and the rates are
taken over the same illumination time. -/
noncomputable def quantumYieldPercent (electronsPerCO coRate photonRate : ℝ) : ℝ :=
  electronsPerCO * coRate / photonRate * 100

/-- The 3.8% loading relation determines the catalyst mass in the 10 mg
sample: `m_cat = ω_cat · m_support / (100 − ω_cat)`. -/
theorem catalyst_mass_of_loading
    {omegaCat supportMass catalystMass : ℝ}
    (hOmegaCat : omegaCat = 3.8)
    (hSupportMass : supportMass = 0.01)
    (hLoading : massFractionPercent catalystMass supportMass = omegaCat) :
    catalystMass = omegaCat * supportMass / (100 - omegaCat) := by
  unfold massFractionPercent at hLoading
  rw [hOmegaCat, hSupportMass] at hLoading
  have hne : catalystMass + (0.01 : ℝ) ≠ 0 := by
    intro hz
    rw [hz, div_zero, zero_mul] at hLoading
    norm_num at hLoading
  rw [hOmegaCat, hSupportMass]
  field_simp at hLoading ⊢
  linarith

/-- Rubric checkpoint: the CO formation rate of the illuminated sample equals
the recorded `9.48e14 s⁻¹` at its printed last digit. -/
theorem co_formation_rate_value
    {avogadro omegaCat supportMass molarMassCat tof catalystMass : ℝ}
    (hAvogadro : avogadro = 6.02e23)
    (hOmegaCat : omegaCat = 3.8)
    (hSupportMass : supportMass = 0.01)
    (hMolarMassCat : molarMassCat = 557.21)
    (hTof : tof = 8)
    (hCatalystMassPos : 0 < catalystMass)
    (hLoading : massFractionPercent catalystMass supportMass = omegaCat) :
    |coFormationRate tof (catalystMolecules avogadro catalystMass molarMassCat)
        - 9.48e14| ≤ 0.01e14 := by
  have hm := catalyst_mass_of_loading hOmegaCat hSupportMass hLoading
  subst hAvogadro; subst hOmegaCat; subst hSupportMass; subst hMolarMassCat; subst hTof
  rw [hm]
  unfold coFormationRate catalystMolecules
  norm_num

/-- Rubric checkpoint: the 390 nm photon energy `h·c/λ` equals the recorded
`5.1e-19 J` at its printed precision. -/
theorem photon_energy_value
    {planckConstant speedOfLight wavelength : ℝ}
    (hPlanckConstant : planckConstant = 6.626e-34)
    (hSpeedOfLight : speedOfLight = 3.00e8)
    (hWavelength : wavelength = 390e-9) :
    |photonEnergy planckConstant speedOfLight wavelength - 5.1e-19| ≤ 0.01e-19 := by
  subst hPlanckConstant; subst hSpeedOfLight; subst hWavelength
  unfold photonEnergy
  norm_num

/-- Rubric checkpoint: the incident photon rate of the 50 mW LED equals the
recorded `9.8e16 s⁻¹` at its printed last digit. -/
theorem incident_photon_rate_value
    {planckConstant speedOfLight wavelength power : ℝ}
    (hPlanckConstant : planckConstant = 6.626e-34)
    (hSpeedOfLight : speedOfLight = 3.00e8)
    (hWavelength : wavelength = 390e-9)
    (hPower : power = 50e-3) :
    |incidentPhotonRate power (photonEnergy planckConstant speedOfLight wavelength)
        - 9.8e16| ≤ 0.01e16 := by
  subst hPlanckConstant; subst hSpeedOfLight; subst hWavelength; subst hPower
  unfold incidentPhotonRate photonEnergy
  norm_num

/-- **IChO 2026 T8.6.** The quantum yield for CO formation, computed from the
loading relation, the TOF law, the photon energy law and equation 8.6.1,
satisfies `|φ − 1.93| < 0.005` (percentage points): the raw value
`φ = 1.9334888…%` rounds to `1.93%` by the standard nearest-two-decimal rule.
The official rubric prints `1.94%`; that figure is recorded in the module
docstring only, since it is not the two-decimal rounding of the computed
value (see the source-inconsistency note there). -/
theorem quantum_yield_co_formation
    {avogadro planckConstant speedOfLight : ℝ}
    {omegaCat supportMass molarMassCat tof wavelength power : ℝ}
    {electronsPerCO catalystMass : ℝ}
    (hAvogadro : avogadro = 6.02e23)
    (hPlanckConstant : planckConstant = 6.626e-34)
    (hSpeedOfLight : speedOfLight = 3.00e8)
    (hOmegaCat : omegaCat = 3.8)
    (hSupportMass : supportMass = 0.01)
    (hMolarMassCat : molarMassCat = 557.21)
    (hTof : tof = 8)
    (hWavelength : wavelength = 390e-9)
    (hPower : power = 50e-3)
    (hElectronsPerCO : electronsPerCO = 2)
    (hCatalystMassPos : 0 < catalystMass)
    (hLoading : massFractionPercent catalystMass supportMass = omegaCat) :
    |quantumYieldPercent electronsPerCO
        (coFormationRate tof (catalystMolecules avogadro catalystMass molarMassCat))
        (incidentPhotonRate power (photonEnergy planckConstant speedOfLight wavelength))
        - 1.93| < 0.005 := by
  have hm := catalyst_mass_of_loading hOmegaCat hSupportMass hLoading
  subst hAvogadro; subst hPlanckConstant; subst hSpeedOfLight; subst hOmegaCat
  subst hSupportMass; subst hMolarMassCat; subst hTof; subst hWavelength; subst hPower
  subst hElectronsPerCO
  rw [hm]
  unfold quantumYieldPercent coFormationRate catalystMolecules incidentPhotonRate photonEnergy
  norm_num

/-- Raw-value pin for **IChO 2026 T8.6**: with the same data, the computed
quantum yield lies within `5×10⁻⁵` percentage points of `1.9335`, recording
`φ_raw = 1.9334888…%` at four decimals. -/
theorem quantum_yield_co_formation_raw_value
    {avogadro planckConstant speedOfLight : ℝ}
    {omegaCat supportMass molarMassCat tof wavelength power : ℝ}
    {electronsPerCO catalystMass : ℝ}
    (hAvogadro : avogadro = 6.02e23)
    (hPlanckConstant : planckConstant = 6.626e-34)
    (hSpeedOfLight : speedOfLight = 3.00e8)
    (hOmegaCat : omegaCat = 3.8)
    (hSupportMass : supportMass = 0.01)
    (hMolarMassCat : molarMassCat = 557.21)
    (hTof : tof = 8)
    (hWavelength : wavelength = 390e-9)
    (hPower : power = 50e-3)
    (hElectronsPerCO : electronsPerCO = 2)
    (hCatalystMassPos : 0 < catalystMass)
    (hLoading : massFractionPercent catalystMass supportMass = omegaCat) :
    |quantumYieldPercent electronsPerCO
        (coFormationRate tof (catalystMolecules avogadro catalystMass molarMassCat))
        (incidentPhotonRate power (photonEnergy planckConstant speedOfLight wavelength))
        - 1.9335| < 5e-5 := by
  have hm := catalyst_mass_of_loading hOmegaCat hSupportMass hLoading
  subst hAvogadro; subst hPlanckConstant; subst hSpeedOfLight; subst hOmegaCat
  subst hSupportMass; subst hMolarMassCat; subst hTof; subst hWavelength; subst hPower
  subst hElectronsPerCO
  rw [hm]
  unfold quantumYieldPercent coFormationRate catalystMolecules incidentPhotonRate photonEnergy
  norm_num

/-- Rubric printed-intermediate evaluation for **IChO 2026 T8.6**: evaluating
equation 8.6.1 with the marking scheme's rounded checkpoints taken as data
(`z = 2`, `r_CO = 9.48e14 s⁻¹`, `r_photon = 9.8e16 s⁻¹`) gives exactly
`φ_printed = 474/245 % = 1.9346939…%`, which also rounds to `1.93%` by the
standard nearest-two-decimal rule — not to the rubric-printed `1.94%`. -/
theorem quantum_yield_printed_intermediates
    {electronsPerCO coRate photonRate : ℝ}
    (hElectronsPerCO : electronsPerCO = 2)
    (hCoRate : coRate = 9.48e14)
    (hPhotonRate : photonRate = 9.8e16) :
    quantumYieldPercent electronsPerCO coRate photonRate = 474 / 245 ∧
      |quantumYieldPercent electronsPerCO coRate photonRate - 1.93| < 0.005 := by
  subst hElectronsPerCO; subst hCoRate; subst hPhotonRate
  unfold quantumYieldPercent
  refine ⟨?_, ?_⟩ <;> norm_num

end IChO2026T8A6
