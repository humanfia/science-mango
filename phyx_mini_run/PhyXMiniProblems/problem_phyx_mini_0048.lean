import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# Reflected-light streak from a dressing mirror

The closet door and floor are viewed in a vertical cross-section.  Physical
lengths are dimensionful quantities, and scalar coordinates are their SI-metre
readouts.  The two boundary rays reflect at the lower and upper edges of the
mirror and meet the floor on the room side of the door.

The supplied image is a refraction diagram unrelated to the closet-mirror
scenario.  Its labelled indices and angles are retained below as a separate
auxiliary readout, but they are not used to derive the mirror answer.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0048

open Dimension CarriesDimension UnitChoices

/-- A real-valued physical quantity carrying the dimension of length. -/
abbrev LengthQuantity := Dimensionful (WithDim L𝓭 ℝ)

/-- Turn an SI-metre scalar readout into a dimensionful physical length. -/
noncomputable def metres (value : ℝ) : LengthQuantity :=
  toDimensionful SI ⟨value⟩

/-- Read a physical length as a real number of SI metres. -/
noncomputable def siMetres (length : LengthQuantity) : ℝ :=
  (length SI).val

/-- Convert the degree readout printed in the auxiliary figure to radians. -/
def degrees (value : ℝ) : ℝ :=
  value * Real.pi / 180

/-! ## Auxiliary figure readout -/

/--
The labels visible in the supplied image.  The image shows an air--slab--air
refraction problem: `surfaceAngleRadians` is the marked `30°` angle from the
interface, while `theta₁`, `theta₂`, and `theta₃` are measured from interface
normals.
-/
structure AuxiliaryRefractionFigure where
  upperRefractiveIndex : ℝ
  slabRefractiveIndex : ℝ
  lowerRefractiveIndex : ℝ
  surfaceAngleRadians : ℝ
  theta₁Radians : ℝ
  theta₂Radians : ℝ
  theta₃Radians : ℝ

/-- Numerical and complementary-angle data read directly from the image. -/
def MatchesAuxiliaryRefractionFigure
    (figure : AuxiliaryRefractionFigure) : Prop :=
  figure.upperRefractiveIndex = 1 ∧
    figure.slabRefractiveIndex = 3 / 2 ∧
    figure.lowerRefractiveIndex = 1 ∧
    figure.surfaceAngleRadians = degrees 30 ∧
    figure.theta₁Radians + figure.surfaceAngleRadians = Real.pi / 2

/-- The two Snell-law relations for the auxiliary air--slab--air diagram. -/
def ObeysAuxiliarySnellLaw (figure : AuxiliaryRefractionFigure) : Prop :=
  figure.upperRefractiveIndex * Real.sin figure.theta₁Radians =
      figure.slabRefractiveIndex * Real.sin figure.theta₂Radians ∧
    figure.slabRefractiveIndex * Real.sin figure.theta₂Radians =
      figure.lowerRefractiveIndex * Real.sin figure.theta₃Radians

/-! ## Dressing-mirror model -/

/--
The four dimensionful measurements in the stated closet-mirror scenario.
No field stores either floor endpoint or the requested streak length.
-/
structure DressingMirrorSetup where
  mirrorHeight : LengthQuantity
  mirrorBottomHeightAboveFloor : LengthQuantity
  bulbDistanceFromDoor : LengthQuantity
  bulbHeightAboveFloor : LengthQuantity

/-- Height of the upper edge of the mirror above the floor. -/
noncomputable def mirrorTopHeightAboveFloor
    (setup : DressingMirrorSetup) : LengthQuantity :=
  metres
    (siMetres setup.mirrorBottomHeightAboveFloor +
      siMetres setup.mirrorHeight)

/-- The calibrated SI-metre measurements stated in the problem. -/
def MatchesClosetMirrorData (setup : DressingMirrorSetup) : Prop :=
  siMetres setup.mirrorHeight = 3 / 2 ∧
    siMetres setup.mirrorBottomHeightAboveFloor = 1 / 2 ∧
    siMetres setup.bulbDistanceFromDoor = 1 ∧
    siMetres setup.bulbHeightAboveFloor = 5 / 2

/-- Positivity and vertical ordering required by the depicted physical setup. -/
def HasPhysicalClosetMirrorGeometry (setup : DressingMirrorSetup) : Prop :=
  0 < siMetres setup.mirrorHeight ∧
    0 ≤ siMetres setup.mirrorBottomHeightAboveFloor ∧
    0 < siMetres setup.bulbDistanceFromDoor ∧
    siMetres (mirrorTopHeightAboveFloor setup) <
      siMetres setup.bulbHeightAboveFloor

/--
A reflected ray recorded by the height at which it meets the vertical mirror
and the horizontal distance from the door at which it reaches the floor.
-/
structure ReflectedFloorRay where
  mirrorHitHeightAboveFloor : LengthQuantity
  floorHitDistanceFromDoor : LengthQuantity

/-- A ray hits the finite mirror and reaches the floor on the room side. -/
def IsPhysicalReflectedFloorRay
    (setup : DressingMirrorSetup) (ray : ReflectedFloorRay) : Prop :=
  siMetres setup.mirrorBottomHeightAboveFloor ≤
      siMetres ray.mirrorHitHeightAboveFloor ∧
    siMetres ray.mirrorHitHeightAboveFloor ≤
      siMetres (mirrorTopHeightAboveFloor setup) ∧
    0 ≤ siMetres ray.floorHitDistanceFromDoor

/--
The planar-mirror reflection law in virtual-image form.

Reflect the bulb across the vertical mirror to the same perpendicular distance
behind the door.  A reflected ray, continued backward, is a straight line from
that virtual image through the mirror hit.  Similar triangles give the stated
relation between the mirror-hit height and the floor-hit distance.  This is a
general ray law and contains neither boundary-ray endpoint nor streak answer.
-/
structure ObeysPlanarMirrorReflection
    (setup : DressingMirrorSetup) (ray : ReflectedFloorRay) : Prop where
  virtualImageCollinearity :
    (siMetres setup.bulbHeightAboveFloor -
        siMetres ray.mirrorHitHeightAboveFloor) *
        siMetres ray.floorHitDistanceFromDoor =
      siMetres setup.bulbDistanceFromDoor *
        siMetres ray.mirrorHitHeightAboveFloor

/-- The near boundary ray reflects at the mirror's lower edge. -/
def IsLowerBoundaryRay
    (setup : DressingMirrorSetup) (ray : ReflectedFloorRay) : Prop :=
  siMetres ray.mirrorHitHeightAboveFloor =
    siMetres setup.mirrorBottomHeightAboveFloor

/-- The far boundary ray reflects at the mirror's upper edge. -/
def IsUpperBoundaryRay
    (setup : DressingMirrorSetup) (ray : ReflectedFloorRay) : Prop :=
  siMetres ray.mirrorHitHeightAboveFloor =
    siMetres (mirrorTopHeightAboveFloor setup)

/--
The physical length of the illuminated floor interval, from the lower-edge
boundary ray's floor hit to the upper-edge boundary ray's floor hit.
-/
noncomputable def floorStreakLength
    (nearRay farRay : ReflectedFloorRay) : LengthQuantity :=
  metres
    (siMetres farRay.floorHitDistanceFromDoor -
      siMetres nearRay.floorHitDistanceFromDoor)

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The SI-metre readout printed beside each answer choice. -/
def AnswerChoice.lengthMetres : AnswerChoice → ℝ
  | .A => 643 / 100
  | .B => 15 / 4
  | .C => 639 / 100
  | .D => 533 / 100

/-- A physical length agrees exactly with a displayed answer choice. -/
def MatchesAnswerChoice
    (length : LengthQuantity) (choice : AnswerChoice) : Prop :=
  siMetres length = choice.lengthMetres

/-- The lower-edge boundary ray reaches the floor `0.25 m` from the door. -/
lemma lowerBoundaryRay_floorDistance
    (setup : DressingMirrorSetup) (nearRay : ReflectedFloorRay)
    (hData : MatchesClosetMirrorData setup)
    (hGeometry : HasPhysicalClosetMirrorGeometry setup)
    (hPhysical : IsPhysicalReflectedFloorRay setup nearRay)
    (hBoundary : IsLowerBoundaryRay setup nearRay)
    (hReflection : ObeysPlanarMirrorReflection setup nearRay) :
    siMetres nearRay.floorHitDistanceFromDoor = 1 / 4 := by
  unfold MatchesClosetMirrorData at hData
  unfold IsLowerBoundaryRay at hBoundary
  rcases hData with ⟨hHeight, hBottom, hDistance, hBulbHeight⟩
  have hReflection' := hReflection.virtualImageCollinearity
  rw [hBulbHeight, hBoundary, hBottom, hDistance] at hReflection'
  norm_num at hReflection' ⊢
  linarith

/-- The upper-edge boundary ray reaches the floor `4.00 m` from the door. -/
lemma upperBoundaryRay_floorDistance
    (setup : DressingMirrorSetup) (farRay : ReflectedFloorRay)
    (hData : MatchesClosetMirrorData setup)
    (hGeometry : HasPhysicalClosetMirrorGeometry setup)
    (hPhysical : IsPhysicalReflectedFloorRay setup farRay)
    (hBoundary : IsUpperBoundaryRay setup farRay)
    (hReflection : ObeysPlanarMirrorReflection setup farRay) :
    siMetres farRay.floorHitDistanceFromDoor = 4 := by
  unfold MatchesClosetMirrorData at hData
  unfold IsUpperBoundaryRay at hBoundary
  rcases hData with ⟨hHeight, hBottom, hDistance, hBulbHeight⟩
  have siMetres_metres (x : ℝ) : siMetres (metres x) = x := by
    simp [siMetres, metres, toDimensionful_apply_apply]
  have hTop : siMetres (mirrorTopHeightAboveFloor setup) = 2 := by
    rw [mirrorTopHeightAboveFloor, siMetres_metres, hBottom, hHeight]
    norm_num
  have hReflection' := hReflection.virtualImageCollinearity
  rw [hBulbHeight, hBoundary, hTop, hDistance] at hReflection'
  norm_num at hReflection' ⊢
  linarith

/--
The reflected-light streak extends from `0.25 m` to `4.00 m`, so its physical
length has SI readout `3.75 m` and agrees with answer choice B.

This formalizes `thm:physics:phyx_mini_0048:target`.
-/
theorem reflected_light_streak_length
    (setup : DressingMirrorSetup)
    (nearRay farRay : ReflectedFloorRay)
    (hData : MatchesClosetMirrorData setup)
    (hGeometry : HasPhysicalClosetMirrorGeometry setup)
    (hNearPhysical : IsPhysicalReflectedFloorRay setup nearRay)
    (hFarPhysical : IsPhysicalReflectedFloorRay setup farRay)
    (hNearBoundary : IsLowerBoundaryRay setup nearRay)
    (hFarBoundary : IsUpperBoundaryRay setup farRay)
    (hNearReflection : ObeysPlanarMirrorReflection setup nearRay)
    (hFarReflection : ObeysPlanarMirrorReflection setup farRay) :
    siMetres (floorStreakLength nearRay farRay) = 15 / 4 ∧
      MatchesAnswerChoice (floorStreakLength nearRay farRay) .B := by
  have hNear := lowerBoundaryRay_floorDistance setup nearRay hData hGeometry
    hNearPhysical hNearBoundary hNearReflection
  have hFar := upperBoundaryRay_floorDistance setup farRay hData hGeometry
    hFarPhysical hFarBoundary hFarReflection
  have siMetres_metres (x : ℝ) : siMetres (metres x) = x := by
    simp [siMetres, metres, toDimensionful_apply_apply]
  have hLength : siMetres (floorStreakLength nearRay farRay) = 15 / 4 := by
    rw [floorStreakLength, siMetres_metres, hFar, hNear]
    norm_num
  exact
    ⟨hLength,
      by simpa [MatchesAnswerChoice, AnswerChoice.lengthMetres] using hLength⟩

end PhyXMiniProblems.ProblemPhyXMini0048
