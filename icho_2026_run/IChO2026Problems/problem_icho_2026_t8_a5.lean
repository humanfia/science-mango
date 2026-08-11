import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T8-A5: surface density of molecular catalyst 1

All scalar quantities in this file are numerical readouts in the units printed
in the question: masses are in `g`, surface area is in `m²`, specific surface
area is in `m² g⁻¹`, and molar mass is in `g mol⁻¹`.  Species identity is kept
separate from these numerical quantities.
-/

namespace IChO2026Problems.T8A5

noncomputable section

/-- The support material named in T8. -/
private inductive SupportMaterial where
  | carbonNitride
  deriving DecidableEq, Repr

/-- The molecular CO₂-reduction catalyst named `1` in T8. -/
private inductive MolecularCatalyst where
  | catalyst1
  deriving DecidableEq, Repr

/-- A macroscopic sample consisting of a molecular catalyst loaded on a
support.  Its two masses are deliberately not combined: the stated loading is
defined using their sum. -/
private structure LoadedCatalystSample where
  support : SupportMaterial
  catalyst : MolecularCatalyst
  supportMass : ℝ
  catalystMass : ℝ
  supportMass_positive : 0 < supportMass
  catalystMass_positive : 0 < catalystMass

/-- The catalyst mass fraction in a loaded sample. -/
private def catalystMassFraction (sample : LoadedCatalystSample) : ℝ :=
  sample.catalystMass / (sample.catalystMass + sample.supportMass)

/-- One square nanometre expressed in square metres. -/
private def oneSquareNanometreInSquareMetres : ℝ :=
  1 / (10 : ℝ) ^ 18

/-- The numerical inputs and standard constant used for T8-A5.  The Avogadro
constant is recorded at the `6.02 × 10²³ mol⁻¹` precision used in the official
calculation; it is an explicit empirical input, rather than an assumption
about the reported molecular surface density. -/
private structure CatalystLoadingExperiment where
  sample : LoadedCatalystSample
  specificSurfaceArea : ℝ
  catalystMolarMass : ℝ
  avogadroConstant : ℝ
  support_is_carbonNitride : sample.support = .carbonNitride
  catalyst_is_catalyst1 : sample.catalyst = .catalyst1
  catalystMassFraction_value : catalystMassFraction sample = 0.038
  specificSurfaceArea_value : specificSurfaceArea = 17.8
  catalystMolarMass_value : catalystMolarMass = 557.21
  avogadroConstant_value : avogadroConstant = 6.02 * 10 ^ 23
  specificSurfaceArea_positive : 0 < specificSurfaceArea
  catalystMolarMass_positive : 0 < catalystMolarMass
  avogadroConstant_positive : 0 < avogadroConstant

/-- A one-square-nanometre patch of the loaded support.  The surface-area law
keeps the conversion from specific area to support mass explicit.  The
equal-mass-fraction condition formalizes the uniform-loading assumption used
by the calculation. -/
private structure LoadedSurfacePatch (experiment : CatalystLoadingExperiment) where
  area : ℝ
  supportMass : ℝ
  catalystMass : ℝ
  area_is_one_square_nanometre : area = oneSquareNanometreInSquareMetres
  specific_surface_area_law : area = experiment.specificSurfaceArea * supportMass
  same_mass_fraction_as_bulk :
    catalystMass / (catalystMass + supportMass) =
      catalystMassFraction experiment.sample
  supportMass_positive : 0 < supportMass
  catalystMass_positive : 0 < catalystMass

/-- The number of catalyst molecules carried by a patch, computed from its
catalyst mass, the supplied molar mass, and Avogadro's constant. -/
private def catalyticMoleculesOnPatch
    (experiment : CatalystLoadingExperiment)
    (patch : LoadedSurfacePatch experiment) : ℝ :=
  patch.catalystMass / experiment.catalystMolarMass * experiment.avogadroConstant

/-- A numerical value reported to one decimal place. -/
private def RoundsToOneDecimal (value reported : ℝ) : Prop :=
  |value - reported| ≤ (1 : ℝ) / 20

/-- T8-A5.  The source's mass-fraction law and specific-surface-area law imply
that one nm² of the C₃N₄-supported catalyst carries approximately `2.4`
molecules of catalyst 1. -/
theorem catalytic_molecules_per_square_nanometre
    (experiment : CatalystLoadingExperiment)
    (patch : LoadedSurfacePatch experiment) :
    RoundsToOneDecimal (catalyticMoleculesOnPatch experiment patch) 2.4 := by
  have hPatchFraction :
      patch.catalystMass / (patch.catalystMass + patch.supportMass) =
        (19 : ℝ) / 500 := by
    calc
      patch.catalystMass / (patch.catalystMass + patch.supportMass) =
          catalystMassFraction experiment.sample :=
        patch.same_mass_fraction_as_bulk
      _ = 0.038 := experiment.catalystMassFraction_value
      _ = (19 : ℝ) / 500 := by norm_num
  have hPatchDenomPositive : 0 < patch.catalystMass + patch.supportMass := by
    exact add_pos patch.catalystMass_positive patch.supportMass_positive
  have hLoading : 481 * patch.catalystMass = 19 * patch.supportMass := by
    have h := hPatchFraction
    field_simp [ne_of_gt hPatchDenomPositive] at h
    linarith
  have hSupportArea :
      (1 : ℝ) / (10 : ℝ) ^ 18 = (17.8 : ℝ) * patch.supportMass := by
    calc
      (1 : ℝ) / (10 : ℝ) ^ 18 = oneSquareNanometreInSquareMetres := rfl
      _ = patch.area := patch.area_is_one_square_nanometre.symm
      _ = experiment.specificSurfaceArea * patch.supportMass :=
        patch.specific_surface_area_law
      _ = (17.8 : ℝ) * patch.supportMass := by
        rw [experiment.specificSurfaceArea_value]
  norm_num at hSupportArea
  field_simp at hSupportArea
  have hCatalystMass :
      patch.catalystMass = (95 : ℝ) / 42809000000000000000000 := by
    field_simp
    nlinarith [hLoading, hSupportArea]
  unfold RoundsToOneDecimal catalyticMoleculesOnPatch
  rw [hCatalystMass, experiment.catalystMolarMass_value,
    experiment.avogadroConstant_value]
  norm_num [abs_of_nonneg, abs_of_neg]

end

end IChO2026Problems.T8A5
