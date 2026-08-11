import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T8-A6: quantum yield for photocatalytic CO formation

The numerical fields in this file use the units printed in the problem:
mass in `g`, molar mass in `g mol⁻¹`, wavelength in `nm`, LED power in `W`,
and turnover frequency in `h⁻¹`.  Rates are therefore molecular counts per
second after division by `3600`.  Chemical identities are kept separately
from these scalar readouts.

The source states the experimental data and the definition of quantum yield,
but not numerical values of the physical constants used to evaluate `hc / λ`.
Their product is consequently an explicit hypothesis, rather than an axiom or
an input containing the requested quantum yield.
-/

namespace IChO2026Problems.T8A6

noncomputable section

/-- Chemical species that occur in the acidic CO₂-to-CO half reaction. -/
private inductive ReductionSpecies where
  | carbonDioxide
  | carbonMonoxide
  | proton
  | water
  | electron
  deriving DecidableEq, Repr

/-- The elements whose conservation is relevant to the half reaction. -/
private inductive Element where
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq, Repr

/-- Formal charge of a reaction species. -/
private def ReductionSpecies.formalCharge : ReductionSpecies → ℤ
  | .carbonDioxide => 0
  | .carbonMonoxide => 0
  | .proton => 1
  | .water => 0
  | .electron => -1

/-- Number of atoms of an element in one formula unit of a species. -/
private def ReductionSpecies.atomCount : ReductionSpecies → Element → ℤ
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .hydrogen => 0
  | .carbonDioxide, .oxygen => 2
  | .carbonMonoxide, .carbon => 1
  | .carbonMonoxide, .hydrogen => 0
  | .carbonMonoxide, .oxygen => 1
  | .proton, .carbon => 0
  | .proton, .hydrogen => 1
  | .proton, .oxygen => 0
  | .water, .carbon => 0
  | .water, .hydrogen => 2
  | .water, .oxygen => 1
  | .electron, _ => 0

/-- Signed stoichiometric coefficients for
`CO₂ + 2 H⁺ + 2 e⁻ → CO + H₂O`; reactants have negative coefficients. -/
private def acidicCO2ToCOHalfReaction : ReductionSpecies → ℤ
  | .carbonDioxide => -1
  | .carbonMonoxide => 1
  | .proton => -2
  | .water => 1
  | .electron => -2

/-- Net formal charge of a reaction written with signed coefficients. -/
private def netFormalCharge (reaction : ReductionSpecies → ℤ) : ℤ :=
  reaction .carbonDioxide * ReductionSpecies.formalCharge .carbonDioxide +
    reaction .carbonMonoxide * ReductionSpecies.formalCharge .carbonMonoxide +
      reaction .proton * ReductionSpecies.formalCharge .proton +
        reaction .water * ReductionSpecies.formalCharge .water +
          reaction .electron * ReductionSpecies.formalCharge .electron

/-- Net atom count for a signed reaction coefficient function. -/
private def netElementCount (reaction : ReductionSpecies → ℤ) (element : Element) : ℤ :=
  reaction .carbonDioxide * ReductionSpecies.atomCount .carbonDioxide element +
    reaction .carbonMonoxide * ReductionSpecies.atomCount .carbonMonoxide element +
      reaction .proton * ReductionSpecies.atomCount .proton element +
        reaction .water * ReductionSpecies.atomCount .water element +
          reaction .electron * ReductionSpecies.atomCount .electron element

/-- The two-electron requirement is read from the coefficient of `e⁻` in the
balanced acidic half reaction, rather than being a numerical fit to the yield. -/
private def electronsPerCarbonMonoxide : ℕ :=
  Int.natAbs (acidicCO2ToCOHalfReaction .electron)

/-- The crystalline support material named in T8. -/
private inductive SupportMaterial where
  | carbonNitride
  deriving DecidableEq, Repr

/-- The molecular iron catalyst named `1` in T8. -/
private inductive MolecularCatalyst where
  | catalyst1
  deriving DecidableEq, Repr

/-- One experimental run under LED illumination.  The chemical entities,
experimental readouts, and physical constants are distinct fields. -/
private structure PhotocatalysisExperiment where
  support : SupportMaterial
  catalyst : MolecularCatalyst
  reactant : ReductionSpecies
  product : ReductionSpecies
  supportMass : ℝ
  catalystMass : ℝ
  catalystMolarMass : ℝ
  turnoverFrequency : ℝ
  ledWavelength : ℝ
  ledPower : ℝ
  avogadroConstant : ℝ
  planckConstant : ℝ
  speedOfLight : ℝ
  supportMass_positive : 0 < supportMass
  catalystMass_positive : 0 < catalystMass
  catalystMolarMass_positive : 0 < catalystMolarMass
  turnoverFrequency_positive : 0 < turnoverFrequency
  ledWavelength_positive : 0 < ledWavelength
  ledPower_positive : 0 < ledPower
  avogadroConstant_positive : 0 < avogadroConstant
  planckConstant_positive : 0 < planckConstant
  speedOfLight_positive : 0 < speedOfLight

/-- Catalyst mass fraction in the loaded support/catalyst mixture. -/
private def catalystMassFraction (experiment : PhotocatalysisExperiment) : ℝ :=
  experiment.catalystMass / (experiment.catalystMass + experiment.supportMass)

/-- The problem's experimental conditions, with `10 mg = 0.01 g` and
`50 mW = 0.050 W` made explicit.  No calculated rate, photon flux, or quantum
yield occurs in this source-data predicate. -/
private def PhotocatalysisExperiment.matchesPrintedConditions
    (experiment : PhotocatalysisExperiment) : Prop :=
  experiment.support = .carbonNitride ∧
    experiment.catalyst = .catalyst1 ∧
      experiment.reactant = .carbonDioxide ∧
        experiment.product = .carbonMonoxide ∧
          catalystMassFraction experiment = 0.038 ∧
            experiment.supportMass = 0.01 ∧
              experiment.catalystMolarMass = 557.21 ∧
                experiment.turnoverFrequency = 8 ∧
                  experiment.ledWavelength = 390 ∧
                    experiment.ledPower = 0.050 ∧
                      experiment.avogadroConstant = 6.02 * (10 : ℝ) ^ 23

/-- The product `h c` in `J m` used in the official wavelength-to-photon-energy
calculation.  This is an explicit physical-constant assumption because its
numerical value is not printed in the question. -/
private def PhotocatalysisExperiment.usesOfficialPhotonEnergyConstants
    (experiment : PhotocatalysisExperiment) : Prop :=
  experiment.planckConstant * experiment.speedOfLight =
    1.989 / (10 : ℝ) ^ 25

/-- Seconds in one hour, used to convert the stated TOF from `h⁻¹` to `s⁻¹`. -/
private def secondsPerHour : ℝ := 3600

/-- One nanometre in metres. -/
private def nanometreInMetres : ℝ := 1 / (10 : ℝ) ^ 9

/-- Amount of catalyst in moles. -/
private def catalystAmount (experiment : PhotocatalysisExperiment) : ℝ :=
  experiment.catalystMass / experiment.catalystMolarMass

/-- CO molecules formed per second from catalyst amount, TOF, Avogadro's
constant, and the hour-to-second conversion. -/
private def carbonMonoxideMoleculeRate (experiment : PhotocatalysisExperiment) : ℝ :=
  catalystAmount experiment * experiment.turnoverFrequency *
    experiment.avogadroConstant / secondsPerHour

/-- Energy in joules of one LED photon, computed by `E = h c / λ`. -/
private def photonEnergy (experiment : PhotocatalysisExperiment) : ℝ :=
  experiment.planckConstant * experiment.speedOfLight /
    (experiment.ledWavelength * nanometreInMetres)

/-- Incident photons per second, obtained from LED power divided by one-photon
energy. -/
private def incidentPhotonRate (experiment : PhotocatalysisExperiment) : ℝ :=
  experiment.ledPower / photonEnergy experiment

/-- Reacted electrons per second.  For CO₂-to-CO the balanced half reaction
consumes two electrons for every carbon-monoxide molecule formed. -/
private def reactedElectronRate (experiment : PhotocatalysisExperiment) : ℝ :=
  (electronsPerCarbonMonoxide : ℝ) * carbonMonoxideMoleculeRate experiment

/-- Quantum yield as a percentage, using the source's ratio of reacted
electrons to incident photons. -/
private def quantumYieldPercent (experiment : PhotocatalysisExperiment) : ℝ :=
  reactedElectronRate experiment / incidentPhotonRate experiment * 100

/-- A reported value is accepted within a stated relative error.  This is used
for intermediate figures that the official solution prints with limited
significant figures. -/
private def HasRelativeErrorAtMost (value reported relativeError : ℝ) : Prop :=
  |value - reported| ≤ relativeError * |reported|

/-- Agreement with a reported percentage to within one hundredth of a
percentage point.  The official final result uses rounded intermediate rates. -/
private def AgreesWithinOneHundredth (value reported : ℝ) : Prop :=
  |value - reported| ≤ (1 : ℝ) / 100

/-- From the printed `3.8 %` loading and `10 mg` support mass, the catalyst
mass used in the run is `19 / 48100 g` (about `3.95 × 10⁻⁴ g`). -/
private theorem catalyst_mass_from_loading
    (experiment : PhotocatalysisExperiment)
    (hdata : experiment.matchesPrintedConditions) :
    experiment.catalystMass = (19 : ℝ) / 48100 := by
  rcases hdata with ⟨_, _, _, _, hloading, hsupport, _, _, _, _, _⟩
  change experiment.catalystMass /
      (experiment.catalystMass + experiment.supportMass) = 0.038 at hloading
  rw [hsupport] at hloading
  have hdenom : experiment.catalystMass + 0.01 ≠ 0 := by
    nlinarith [experiment.catalystMass_positive]
  have hmass := (div_eq_iff hdenom).mp hloading
  norm_num at hmass ⊢
  linarith

/-- The catalyst loading, molar mass, TOF, and Avogadro constant yield the
official CO formation rate `9.48 × 10¹⁴ s⁻¹` to the displayed precision. -/
private theorem carbon_monoxide_formation_rate
    (experiment : PhotocatalysisExperiment)
    (hdata : experiment.matchesPrintedConditions) :
    HasRelativeErrorAtMost (carbonMonoxideMoleculeRate experiment)
      (9.48 * (10 : ℝ) ^ 14) ((1 : ℝ) / 1000) := by
  have hmass := catalyst_mass_from_loading experiment hdata
  rcases hdata with ⟨_, _, _, _, _, _, hmolar, htof, _, _, havogadro⟩
  unfold HasRelativeErrorAtMost carbonMonoxideMoleculeRate catalystAmount secondsPerHour
  rw [hmass, hmolar, htof, havogadro]
  norm_num

/-- Applying `E = h c / λ` to the 390 nm LED gives the official photon energy
`5.1 × 10⁻¹⁹ J`. -/
private theorem led_photon_energy
    (experiment : PhotocatalysisExperiment)
    (hdata : experiment.matchesPrintedConditions)
    (hconstants : experiment.usesOfficialPhotonEnergyConstants) :
    photonEnergy experiment = 5.1 / (10 : ℝ) ^ 19 := by
  rcases hdata with ⟨_, _, _, _, _, _, _, _, hwavelength, _, _⟩
  unfold PhotocatalysisExperiment.usesOfficialPhotonEnergyConstants at hconstants
  unfold photonEnergy nanometreInMetres
  rw [hconstants, hwavelength]
  norm_num

/-- The 50 mW LED consequently supplies approximately
`9.8 × 10¹⁶` incident photons per second. -/
private theorem incident_photon_rate
    (experiment : PhotocatalysisExperiment)
    (hdata : experiment.matchesPrintedConditions)
    (hconstants : experiment.usesOfficialPhotonEnergyConstants) :
    HasRelativeErrorAtMost (incidentPhotonRate experiment)
      (9.8 * (10 : ℝ) ^ 16) ((1 : ℝ) / 100) := by
  have henergy := led_photon_energy experiment hdata hconstants
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, hpower, _⟩
  unfold HasRelativeErrorAtMost incidentPhotonRate
  rw [henergy, hpower]
  norm_num

/-- T8-A6: the source's electron/photon definition of quantum yield and the
given experiment yield the reported `1.94 %` for CO formation.  The final
target remains a conclusion; it is not stored in the experimental data. -/
theorem quantum_yield_for_CO_formation
    (experiment : PhotocatalysisExperiment)
    (hdata : experiment.matchesPrintedConditions)
    (hconstants : experiment.usesOfficialPhotonEnergyConstants) :
    AgreesWithinOneHundredth (quantumYieldPercent experiment) 1.94 := by
  have hmass := catalyst_mass_from_loading experiment hdata
  rcases hdata with
    ⟨_, _, _, _, _, _, hmolar, htof, hwavelength, hpower, havogadro⟩
  unfold PhotocatalysisExperiment.usesOfficialPhotonEnergyConstants at hconstants
  unfold AgreesWithinOneHundredth quantumYieldPercent reactedElectronRate
    incidentPhotonRate photonEnergy carbonMonoxideMoleculeRate catalystAmount
    secondsPerHour nanometreInMetres electronsPerCarbonMonoxide acidicCO2ToCOHalfReaction
  rw [hmass, hmolar, htof, hwavelength, hpower, havogadro, hconstants]
  norm_num

end

end IChO2026Problems.T8A6
