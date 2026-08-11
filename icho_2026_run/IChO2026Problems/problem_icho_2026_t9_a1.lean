import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T9-A1: molar mass of β-cyclodextrin

All molar-mass readouts in this file are numerical values in `g mol⁻¹`.
The species and the α-1,4 glycosidic linkage are represented separately from
those scalar readouts.  The official solution calculates the cyclic product
by subtracting one water molecule for every glycosidic linkage.
-/

namespace IChO2026Problems.T9A1

/-- A molar mass represented by its numerical value in `g mol⁻¹`. -/
private abbrev MolarMassGramPerMol := ℝ

/-- The three cyclodextrins identified in the source. -/
private inductive Cyclodextrin where
  | alpha
  | beta
  | gamma
  deriving DecidableEq, Repr

/-- The chemical entities whose masses are relevant to the condensation
calculation. -/
private inductive ChemicalSpecies where
  | glucose
  | water
  | cyclodextrin (kind : Cyclodextrin)
  deriving DecidableEq, Repr

/-- The linkage type stated for the glucose subunits of cyclodextrins. -/
private inductive GlycosidicLinkage where
  | alphaOneFour
  deriving DecidableEq, Repr

/-- Each of the named cyclodextrins consists only of α-1,4-glycosidic
linkages. -/
private def linkageType (_ : Cyclodextrin) : GlycosidicLinkage := .alphaOneFour

/-- Numbers of α-D-glucopyranoside units stated in the problem. -/
private def glucopyranosideUnitCount : Cyclodextrin → ℕ
  | .alpha => 6
  | .beta => 7
  | .gamma => 8

/-- In a cyclic cyclodextrin ring, each glucose unit participates in one
glycosidic linkage, including the ring-closing linkage. -/
private def glycosidicLinkageCount (kind : Cyclodextrin) : ℕ :=
  glucopyranosideUnitCount kind

/-- Empirical molar-mass data used by the official calculation.  The glucose
value is supplied in the question.  The water value is the `18.016 g mol⁻¹`
loss per glycosidic condensation displayed in the official solution; it is an
input datum, not the requested β-CD molar mass. -/
private structure CyclodextrinMolarMassData where
  glucoseMolarMass : MolarMassGramPerMol
  waterMolarMass : MolarMassGramPerMol
  glucose_molarMass_value : glucoseMolarMass = 180.16
  water_molarMass_value : waterMolarMass = 18.016
  glucoseMolarMass_positive : 0 < glucoseMolarMass
  waterMolarMass_positive : 0 < waterMolarMass

/-- The condensation mass balance for a cyclic cyclodextrin: start with the
glucose subunits and remove the water released at every glycosidic linkage. -/
private def cyclodextrinMolarMass
    (data : CyclodextrinMolarMassData) (kind : Cyclodextrin) :
    MolarMassGramPerMol :=
  data.glucoseMolarMass * glucopyranosideUnitCount kind -
    data.waterMolarMass * glycosidicLinkageCount kind

/-- Molar mass of each species relevant to T9-A1. -/
private def molarMass (data : CyclodextrinMolarMassData) :
    ChemicalSpecies → MolarMassGramPerMol
  | .glucose => data.glucoseMolarMass
  | .water => data.waterMolarMass
  | .cyclodextrin kind => cyclodextrinMolarMass data kind

/-- A numerical readout is reported to two decimal places. -/
private def RoundsToTwoDecimalPlaces (value reported : ℝ) : Prop :=
  |value - reported| ≤ (1 : ℝ) / 200

/--
T9-A1.  β-CD contains seven glucose units and seven cyclic glycosidic
linkages.  Thus the exact result from the displayed decimal inputs is
`1135.008 g mol⁻¹`, which reports as `1135.01 g mol⁻¹` to two decimal places.
-/
theorem beta_cyclodextrin_molar_mass
    (data : CyclodextrinMolarMassData) :
    molarMass data (.cyclodextrin .beta) = 1135.008 ∧
      RoundsToTwoDecimalPlaces (molarMass data (.cyclodextrin .beta)) 1135.01 := by
  rw [show molarMass data (.cyclodextrin .beta) =
      data.glucoseMolarMass * 7 - data.waterMolarMass * 7 by rfl,
    data.glucose_molarMass_value, data.water_molarMass_value]
  constructor
  · norm_num
  · norm_num [RoundsToTwoDecimalPlaces]

end IChO2026Problems.T9A1
