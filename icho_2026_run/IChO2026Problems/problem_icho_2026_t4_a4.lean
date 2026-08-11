import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T4-A4: energy released by uranium-235 fission

All energies in this file are numerical readouts in MeV.  The fission reaction
is represented separately from its binding-energy data: nucleon conservation
fixes the total number of nucleons in the two fission products, and the energy
calculation subsequently uses the supplied average binding energies.
-/

namespace IChO2026Problems.T4A4

/-- An energy readout expressed in MeV. -/
private abbrev EnergyMeV := ℝ

/-- A binding energy per nucleon expressed in MeV per nucleon. -/
private abbrev BindingEnergyPerNucleon := ℝ

/-- The two bound nuclear materials whose average binding energies occur in
the calculation.  A free neutron is deliberately not a member: it has no
nuclear binding energy in the approximation specified by the question. -/
private inductive BoundNuclearMaterial where
  | uranium235
  | fissionProducts
  deriving DecidableEq, Repr

/-- The nucleon number of the uranium isotope stated in the problem. -/
private def uranium235NucleonCount : ℕ := 235

/-- A fission reaction of `²³⁵U` after neutron absorption.  The two product
slots express the two fission nuclei found in the preceding reaction part;
their individual identities and mass numbers are not selected here because
the present energy calculation uses only their conserved total. -/
private structure U235FissionReaction where
  firstFissionProductNucleonCount : ℕ
  secondFissionProductNucleonCount : ℕ
  incidentFreeNeutronCount : ℕ
  emittedFreeNeutronCount : ℕ

/-- The total number of bound nucleons distributed between the two fission
products. -/
private def U235FissionReaction.fissionProductNucleonCount
    (reaction : U235FissionReaction) : ℕ :=
  reaction.firstFissionProductNucleonCount +
    reaction.secondFissionProductNucleonCount

/-- The source reaction has one incident neutron, emits three free neutrons,
and conserves nucleon number.  This is a mathematical bridge, not an opaque
label: it is sufficient to infer the product total used below. -/
private def U235FissionReaction.matchesSourceReaction
    (reaction : U235FissionReaction) : Prop :=
  reaction.incidentFreeNeutronCount = 1 ∧
    reaction.emittedFreeNeutronCount = 3 ∧
      uranium235NucleonCount + reaction.incidentFreeNeutronCount =
        reaction.fissionProductNucleonCount + reaction.emittedFreeNeutronCount

/-- Binding-energy data for the initial uranium nucleus, the aggregate fission
products, and a free neutron.  The latter is an energy rather than a
per-nucleon average because it denotes a single unbound particle. -/
private structure FissionBindingEnergyData where
  bindingEnergyPerNucleon : BoundNuclearMaterial → BindingEnergyPerNucleon
  freeNeutronBindingEnergy : EnergyMeV

/-- The supplied binding-energy values.  The zero entry faithfully records the
instruction to neglect the binding energy of each free neutron; it is not a
claimed measured nuclear constant. -/
private def FissionBindingEnergyData.matchesSuppliedData
    (data : FissionBindingEnergyData) : Prop :=
  data.bindingEnergyPerNucleon .uranium235 = 7.59 ∧
    data.bindingEnergyPerNucleon .fissionProducts = 8.45 ∧
      data.freeNeutronBindingEnergy = 0

/-- The total binding energy before fission, including the source-modelled
zero contribution from the incident free neutron. -/
private def initialBindingEnergy (data : FissionBindingEnergyData)
    (reaction : U235FissionReaction) : EnergyMeV :=
  data.bindingEnergyPerNucleon .uranium235 * uranium235NucleonCount +
    data.freeNeutronBindingEnergy * reaction.incidentFreeNeutronCount

/-- The total binding energy after fission, including the source-modelled zero
contribution from the emitted free neutrons. -/
private def finalBindingEnergy (data : FissionBindingEnergyData)
    (reaction : U235FissionReaction) : EnergyMeV :=
  data.bindingEnergyPerNucleon .fissionProducts *
      reaction.fissionProductNucleonCount +
    data.freeNeutronBindingEnergy * reaction.emittedFreeNeutronCount

/-- The released energy is the increase in total binding energy between the
post-fission and pre-fission sides of the reaction. -/
private def releasedFissionEnergy (data : FissionBindingEnergyData)
    (reaction : U235FissionReaction) : EnergyMeV :=
  finalBindingEnergy data reaction - initialBindingEnergy data reaction

/-- With the source reaction stoichiometry and supplied average binding
energies, uranium-235 fission releases `185.2 MeV`.  The positive inequality
records the requested direction, namely energy released rather than absorbed.
Neither the product nucleon total nor the requested energy is stored as an
assumption: the former follows from the conservation equation and the latter
from the binding-energy definitions. -/
theorem uranium235_fission_released_energy
    (reaction : U235FissionReaction) (data : FissionBindingEnergyData)
    (hreaction : reaction.matchesSourceReaction)
    (hdata : data.matchesSuppliedData) :
    releasedFissionEnergy data reaction = 185.2 ∧
      0 < releasedFissionEnergy data reaction := by
  rcases hreaction with ⟨hincident, hemitted, hconservation⟩
  rcases hdata with ⟨huranium, hfissionProducts, hfreeNeutron⟩
  norm_num [uranium235NucleonCount] at hconservation
  have hfissionProductNucleonCount : reaction.fissionProductNucleonCount = 233 := by
    omega
  constructor <;>
    norm_num [releasedFissionEnergy, finalBindingEnergy, initialBindingEnergy,
      uranium235NucleonCount, hfissionProductNucleonCount, huranium,
      hfissionProducts, hfreeNeutron]

end IChO2026Problems.T4A4
