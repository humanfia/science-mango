import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

namespace PhyXMiniProblems.ProblemPhyXMini0106

noncomputable section

open Dimension

/-!
# Apparent size of a seed head inside a spherical resin paperweight

The seed head and the resin boundary are concentric spheres.  The upper and
lower rays in the figure are tangent to the seed head, refract at the spherical
resin--air interface, and emerge parallel to the observer's viewing axis.

All radii and diameters are dimensionful Physlib quantities.  Refractive
indices and sines of the two labelled angles are dimensionless real numbers.
-/

/-- A physical length represented coherently in every choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI unit choices with length readouts expressed in millimetres. -/
def millimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.millimeters }

/-- Read a physical length as a real number of millimetres. -/
def millimetersValue (length : LengthQuantity) : ℝ :=
  (length millimeterUnitChoices).val

/-- The two physical spheres whose common centre is marked in the figure. -/
inductive SphereLabel where
  | seedHead
  | resinBoundary
  deriving DecidableEq, Repr

/-- The optical media on the two sides of the spherical outer interface. -/
inductive OpticalMedium where
  | resin
  | air
  deriving DecidableEq, Repr

/-- The symmetric tangent rays drawn above and below the common centre. -/
inductive FigureRay where
  | upper
  | lower
  deriving DecidableEq, Repr

/--
Physical quantities and labelled incidence geometry for the spherical resin
viewing setup.  `thetaA` is the angle inside the resin between the upper ray
and the spherical-interface normal; `thetaB` is the refracted angle in air.

The abstract geometric relations retain the physical roles of concentricity,
tangency, and the parallel emergent rays without replacing those notions by
untyped scalar flags.
-/
structure SphericalResinViewingSetup where
  radius : SphereLabel → LengthQuantity
  trueDiameter : LengthQuantity
  apparentRadius : LengthQuantity
  apparentDiameter : LengthQuantity
  refractiveIndex : OpticalMedium → ℝ
  thetaA : Real.Angle
  thetaB : Real.Angle
  sharesCenter : SphereLabel → SphereLabel → Prop
  isTangentTo : FigureRay → SphereLabel → Prop
  emergesParallelToViewingAxis : FigureRay → Prop

/--
Numerical readouts stated in the problem.  The seed-head diameter and resin
radius are millimetre readouts, whereas refractive indices are dimensionless.
No apparent radius or apparent diameter occurs in these data.
-/
structure HasProblemReadouts (setup : SphericalResinViewingSetup) : Prop where
  seed_head_diameter_millimeters :
    millimetersValue setup.trueDiameter = 45
  resin_sphere_radius_millimeters :
    millimetersValue (setup.radius .resinBoundary) = 80
  resin_refractive_index : setup.refractiveIndex .resin = (153 : ℝ) / 100
  air_refractive_index : setup.refractiveIndex .air = 1

/--
Qualitative and ray-geometric information read from the concentric-sphere
figure.  In particular, the object lies strictly inside the resin sphere and
its apparent image is enlarged.  The sine inequalities select the physical
acute-angle branch of the displayed refraction geometry.
-/
structure MatchesConcentricSphereFigure
    (setup : SphericalResinViewingSetup) : Prop where
  spheres_are_concentric :
    setup.sharesCenter .seedHead .resinBoundary
  upper_ray_tangent_to_seed_head :
    setup.isTangentTo .upper .seedHead
  lower_ray_tangent_to_seed_head :
    setup.isTangentTo .lower .seedHead
  upper_ray_emerges_parallel :
    setup.emergesParallelToViewingAxis .upper
  lower_ray_emerges_parallel :
    setup.emergesParallelToViewingAxis .lower
  seed_radius_positive :
    ∀ units, 0 < (setup.radius .seedHead units).val
  seed_head_inside_resin_sphere :
    ∀ units,
      (setup.radius .seedHead units).val <
        (setup.radius .resinBoundary units).val
  apparent_radius_larger_than_true_radius :
    ∀ units,
      (setup.radius .seedHead units).val <
        (setup.apparentRadius units).val
  thetaA_is_physical :
    0 < setup.thetaA.sin ∧ setup.thetaA.sin < 1
  thetaB_is_physical :
    0 < setup.thetaB.sin ∧ setup.thetaB.sin < 1

/--
The governing geometry and refraction laws for the ray construction.

For every unit choice, tangency of the internal ray gives
`R sin(thetaA) = r`.  Snell's law at the resin--air interface gives
`n_resin sin(thetaA) = n_air sin(thetaB)`.  Since the emergent ray is parallel
to the viewing axis, its height is the apparent radius
`r' = R sin(thetaB)`.  The remaining two laws relate each diameter to its
radius.  None of these laws assigns a numerical value to the requested
apparent diameter.
-/
structure SatisfiesSphericalRefractionLaws
    (setup : SphericalResinViewingSetup) : Prop where
  refractive_indices_positive :
    ∀ medium, 0 < setup.refractiveIndex medium
  true_diameter_is_twice_radius :
    ∀ units,
      (setup.trueDiameter units).val =
        2 * (setup.radius .seedHead units).val
  tangent_ray_geometry :
    ∀ units,
      (setup.radius .resinBoundary units).val * setup.thetaA.sin =
        (setup.radius .seedHead units).val
  snell_law_at_resin_air_interface :
    setup.refractiveIndex .resin * setup.thetaA.sin =
      setup.refractiveIndex .air * setup.thetaB.sin
  apparent_ray_height_geometry :
    ∀ units,
      (setup.apparentRadius units).val =
        (setup.radius .resinBoundary units).val * setup.thetaB.sin
  apparent_diameter_is_twice_radius :
    ∀ units,
      (setup.apparentDiameter units).val =
        2 * (setup.apparentRadius units).val

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Apparent-diameter readout in millimetres printed for each answer choice. -/
def AnswerChoice.diameterMillimeters : AnswerChoice → ℝ
  | .A => (689 : ℝ) / 10
  | .B => (676 : ℝ) / 10
  | .C => (667 : ℝ) / 10
  | .D => (692 : ℝ) / 10

/--
A physical diameter matches a choice displayed to the nearest tenth of a
millimetre when its readout differs by at most `0.05 mm`.
-/
def MatchesAnswerToNearestTenth
    (diameter : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |millimetersValue diameter - choice.diameterMillimeters| ≤ (1 : ℝ) / 20

/-- The answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/--
The tangency geometry and Snell's law give an exact model readout of
`68.85 mm`; consequently the apparent diameter matches answer A, `68.9 mm`,
at the precision displayed in the problem.

Blueprint label: `thm:physics:phyx_mini_0106:target`.
-/
theorem seed_head_apparent_diameter_matches_answer_A
    (setup : SphericalResinViewingSetup)
    (_readouts : HasProblemReadouts setup)
    (_figure : MatchesConcentricSphereFigure setup)
    (_laws : SatisfiesSphericalRefractionLaws setup) :
    millimetersValue setup.apparentDiameter = (1377 : ℝ) / 20 ∧
      MatchesAnswerToNearestTenth setup.apparentDiameter .A := by
  have apparentDiameterValue :
      millimetersValue setup.apparentDiameter = (1377 : ℝ) / 20 := by
    change
      (setup.apparentDiameter millimeterUnitChoices).val = (1377 : ℝ) / 20
    have trueDiameterValue := _readouts.seed_head_diameter_millimeters
    have resinRadiusValue := _readouts.resin_sphere_radius_millimeters
    have trueDiameterLaw :=
      _laws.true_diameter_is_twice_radius millimeterUnitChoices
    have tangentLaw := _laws.tangent_ray_geometry millimeterUnitChoices
    have snellLaw := _laws.snell_law_at_resin_air_interface
    have apparentRadiusLaw :=
      _laws.apparent_ray_height_geometry millimeterUnitChoices
    have apparentDiameterLaw :=
      _laws.apparent_diameter_is_twice_radius millimeterUnitChoices
    change
      (setup.trueDiameter millimeterUnitChoices).val = 45 at trueDiameterValue
    change
      (setup.radius .resinBoundary millimeterUnitChoices).val = 80 at resinRadiusValue
    rw [trueDiameterValue] at trueDiameterLaw
    rw [resinRadiusValue] at tangentLaw apparentRadiusLaw
    rw [_readouts.resin_refractive_index, _readouts.air_refractive_index] at snellLaw
    nlinarith
  refine ⟨apparentDiameterValue, ?_⟩
  unfold MatchesAnswerToNearestTenth
  rw [apparentDiameterValue]
  norm_num [AnswerChoice.diameterMillimeters]

end

end PhyXMiniProblems.ProblemPhyXMini0106
