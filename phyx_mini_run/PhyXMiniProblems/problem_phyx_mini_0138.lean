import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.LinearAlgebra.Ray
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0138

open Dimension

/-!
# Refraction through a plane-parallel glass slab

A light ray passes from air into a flat, uniformly thick glass slab and then
back into air.  The supplied figure labels the incident angle as `60°`, the
angle inside the slab as `thetaA`, and the emergent angle as `thetaB`; all are
measured from the dashed interface normals.  The glass has refractive index
`1.50`.

Directions are genuine rays (nonzero vectors modulo positive rescaling),
angles are `Real.Angle`s, and the slab thickness is a unit-independent
Physlib length.  Real numbers are used only for the dimensionless refractive
index and numerical readouts.
-/

/-- A unit-independent physical quantity carrying the dimension of length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Meter readout used only to express positivity of the slab thickness. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- A point in the two-dimensional plane of the source ray diagram. -/
abbrev DiagramPoint : Type := Fin 2 → ℝ

/-- An oriented direction in the diagram, modulo positive rescaling. -/
abbrev DiagramRay : Type := Module.Ray ℝ (Fin 2 → ℝ)

/-- Physical kinds of optical medium occurring in the problem. -/
inductive MediumKind where
  | air
  | glass
  deriving DecidableEq, Repr

/-- The three regions, ordered from left to right in the source image. -/
inductive MediumRegion where
  | incidentAir
  | glassSlab
  | emergentAir
  deriving DecidableEq, Repr

/-- The entry and exit faces of the glass slab. -/
inductive SlabFace where
  | entry
  | exit
  deriving DecidableEq, Repr

/-- The solid physical rays and the dashed apparent-image extension. -/
inductive RayLabel where
  | rayFromObject
  | refractedInsideGlass
  | emergentRay
  | apparentImageExtension
  deriving DecidableEq, Repr

/-- Line styles distinguished in the source image. -/
inductive RayStyle where
  | solid
  | dashed
  deriving DecidableEq, Repr

/-- The color used for all ray segments in the source image. -/
inductive FigureColor where
  | magenta
  deriving DecidableEq, Repr

/-- The slab idealization stated in the problem. -/
inductive SlabModel where
  | flatUniformThickness
  deriving DecidableEq, Repr

/--
An optical medium together with its dimensionless refractive index.

Positivity is kept in `HasPhysicalParameters`, so this structure stores data
rather than silently adding a governing hypothesis.
-/
structure OpticalMedium where
  kind : MediumKind
  refractiveIndex : ℝ

/-!
All physical objects and scalar angle readouts named by the problem and its
figure.  `thetaAAtEntry` and `thetaAAtExit` are kept separate so that equality
of the internal angles is supplied by plane-parallel geometry rather than by
definition.  In particular, `thetaB` is an unconstrained field here.
-/
structure ParallelGlassSlabSetup where
  mediumAt : MediumRegion → OpticalMedium
  slabModel : SlabModel
  slabThickness : LengthQuantity
  objectPoint : DiagramPoint
  apparentImagePoint : DiagramPoint
  pointOnFace : SlabFace → DiagramPoint
  faceNormal : SlabFace → DiagramRay
  rayOrigin : RayLabel → DiagramPoint
  rayDirection : RayLabel → DiagramRay
  rayStyle : RayLabel → RayStyle
  rayColor : RayLabel → FigureColor
  incidentAngle : Real.Angle
  thetaAAtEntry : Real.Angle
  thetaAAtExit : Real.Angle
  thetaB : Real.Angle

/-- A refraction angle represented by its nonnegative acute real lift. -/
def IsPhysicalRefractionAngle (theta : Real.Angle) : Prop :=
  0 ≤ theta.toReal ∧ theta.toReal ≤ Real.pi / 2

/-!
Positivity and the angular branch appropriate to ordinary air/glass
refraction.  These conditions select the physically relevant solution of the
sine equations without assigning a numerical value to `thetaB`.
-/
def HasPhysicalParameters (setup : ParallelGlassSlabSetup) : Prop :=
  (∀ region : MediumRegion,
      0 < (setup.mediumAt region).refractiveIndex) ∧
    0 < lengthInMeters setup.slabThickness ∧
    IsPhysicalRefractionAngle setup.incidentAngle ∧
    IsPhysicalRefractionAngle setup.thetaAAtEntry ∧
    IsPhysicalRefractionAngle setup.thetaAAtExit ∧
    IsPhysicalRefractionAngle setup.thetaB

/-!
Problem-text data: air on both sides, glass in the middle, glass index `1.50`,
and incident angle `60° = pi/3`.  The two air regions are modeled as the same
medium; no emergent-angle value occurs here.
-/
def MatchesProblemReadouts (setup : ParallelGlassSlabSetup) : Prop :=
  (setup.mediumAt .incidentAir).kind = .air ∧
    (setup.mediumAt .glassSlab).kind = .glass ∧
    (setup.mediumAt .emergentAir).kind = .air ∧
    setup.mediumAt .incidentAir = setup.mediumAt .emergentAir ∧
    (setup.mediumAt .glassSlab).refractiveIndex = 3 / 2 ∧
    setup.incidentAngle = ((Real.pi / 3 : ℝ) : Real.Angle)

/-!
Qualitative and geometric information read from the primary image: a flat
uniform slab, solid physical ray segments, a dashed backward extension to the
apparent image, and magenta coloring.  The extension has the emergent ray's
direction.  None of these readouts prescribes `thetaB`.
-/
def MatchesSuppliedFigure (setup : ParallelGlassSlabSetup) : Prop :=
  setup.slabModel = .flatUniformThickness ∧
    setup.rayOrigin .rayFromObject = setup.objectPoint ∧
    setup.rayOrigin .refractedInsideGlass = setup.pointOnFace .entry ∧
    setup.rayOrigin .emergentRay = setup.pointOnFace .exit ∧
    setup.rayOrigin .apparentImageExtension = setup.apparentImagePoint ∧
    setup.rayStyle .rayFromObject = .solid ∧
    setup.rayStyle .refractedInsideGlass = .solid ∧
    setup.rayStyle .emergentRay = .solid ∧
    setup.rayStyle .apparentImageExtension = .dashed ∧
    (∀ ray : RayLabel, setup.rayColor ray = .magenta) ∧
    setup.rayDirection .apparentImageExtension =
      setup.rayDirection .emergentRay

/-!
Plane-parallel slab geometry.  The equal face normals transfer the internal
angle at the entry face to the incidence angle at the exit face.  This is a
geometric law and does not state the requested external emergent angle.
-/
structure SatisfiesPlaneParallelGeometry
    (setup : ParallelGlassSlabSetup) : Prop where
  parallelFaceNormals : setup.faceNormal .entry = setup.faceNormal .exit
  internalAngleTransfer : setup.thetaAAtExit = setup.thetaAAtEntry

/--
Snell's law at one interface, `n₁ sin(theta₁) = n₂ sin(theta₂)`.

No matching optics declaration was available in Mathlib/PhysLean, so this
local predicate records the physical law directly.
-/
def SnellLawAtInterface
    (incoming outgoing : OpticalMedium)
    (incidentAngle refractedAngle : Real.Angle) : Prop :=
  incoming.refractiveIndex * Real.Angle.sin incidentAngle =
    outgoing.refractiveIndex * Real.Angle.sin refractedAngle

/-!
Snell's law at both air/glass interfaces.  The second equation uses the
separate internal exit angle; plane-parallel geometry relates it to
`thetaAAtEntry`.
-/
structure SatisfiesSnellsLaw (setup : ParallelGlassSlabSetup) : Prop where
  entryFaceLaw :
    SnellLawAtInterface
      (setup.mediumAt .incidentAir) (setup.mediumAt .glassSlab)
      setup.incidentAngle setup.thetaAAtEntry
  exitFaceLaw :
    SnellLawAtInterface
      (setup.mediumAt .glassSlab) (setup.mediumAt .emergentAir)
      setup.thetaAAtExit setup.thetaB

/-- Labels of the four dimensionless values printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless number printed beside each answer label. -/
def displayedAnswerValue : AnswerChoice → ℝ
  | .A => 666 / 1000
  | .B => 966 / 1000
  | .C => 866 / 1000
  | .D => 766 / 1000

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
The displayed decimals are dimensionless and choice C is the nearest-
thousandth value of `sin(thetaB)`.  This explicitly separates the source's
decimal choice from the angle itself, whose exact radian value is the primary
target.
-/
def MatchesDisplayedSineToNearestThousandth
    (setup : ParallelGlassSlabSetup) (choice : AnswerChoice) : Prop :=
  |Real.Angle.sin setup.thetaB - displayedAnswerValue choice| ≤ 1 / 2000

/-- A choice is the unique displayed nearest-thousandth sine value. -/
def IsUniqueMatchingDisplayedSine
    (setup : ParallelGlassSlabSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedSineToNearestThousandth setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedSineToNearestThousandth setup other → other = choice

/-!
For a plane-parallel slab surrounded by the same medium, the two Snell-law
equations cancel the glass refraction and give equal incident and emergent
angles on the physical acute branch.
-/
lemma emergentAngle_eq_incidentAngle
    (setup : ParallelGlassSlabSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_problem : MatchesProblemReadouts setup)
    (h_geometry : SatisfiesPlaneParallelGeometry setup)
    (h_snell : SatisfiesSnellsLaw setup) :
    setup.thetaB = setup.incidentAngle := by
  rcases h_physical with
    ⟨h_index_pos, _, h_incident_physical, _, _, h_thetaB_physical⟩
  rcases h_problem with ⟨_, _, _, h_same_air, _, _⟩
  have h_entry := h_snell.entryFaceLaw
  have h_exit := h_snell.exitFaceLaw
  change
    (setup.mediumAt .incidentAir).refractiveIndex *
        Real.Angle.sin setup.incidentAngle =
      (setup.mediumAt .glassSlab).refractiveIndex *
        Real.Angle.sin setup.thetaAAtEntry at h_entry
  change
    (setup.mediumAt .glassSlab).refractiveIndex *
        Real.Angle.sin setup.thetaAAtExit =
      (setup.mediumAt .emergentAir).refractiveIndex *
        Real.Angle.sin setup.thetaB at h_exit
  rw [h_geometry.internalAngleTransfer, ← h_same_air] at h_exit
  have h_scaled_sine :
      (setup.mediumAt .incidentAir).refractiveIndex *
          Real.Angle.sin setup.incidentAngle =
        (setup.mediumAt .incidentAir).refractiveIndex *
          Real.Angle.sin setup.thetaB :=
    h_entry.trans h_exit
  have h_sine :
      Real.Angle.sin setup.incidentAngle =
        Real.Angle.sin setup.thetaB :=
    mul_left_cancel₀ (h_index_pos .incidentAir).ne' h_scaled_sine
  have h_sine_real :
      Real.sin setup.incidentAngle.toReal =
        Real.sin setup.thetaB.toReal := by
    simpa using h_sine
  have h_toReal :
      setup.incidentAngle.toReal = setup.thetaB.toReal :=
    Real.injOn_sin
      ⟨by linarith [h_incident_physical.1, Real.pi_pos],
        h_incident_physical.2⟩
      ⟨by linarith [h_thetaB_physical.1, Real.pi_pos],
        h_thetaB_physical.2⟩
      h_sine_real
  calc
    setup.thetaB = (setup.thetaB.toReal : Real.Angle) :=
      (Real.Angle.coe_toReal setup.thetaB).symm
    _ = (setup.incidentAngle.toReal : Real.Angle) :=
      congrArg (fun x : ℝ => (x : Real.Angle)) h_toReal.symm
    _ = setup.incidentAngle := Real.Angle.coe_toReal setup.incidentAngle

/-!
The outgoing ray is parallel to the incident ray, so `thetaB = 60° = pi/3`.
Consequently its sine is exactly `sqrt 3 / 2`, whose nearest-thousandth
displayed value is `0.866`, uniquely selecting answer C.

This formalizes `thm:physics:phyx_mini_0138:target`.  The value of `thetaB`,
its sine, and answer C occur only in conclusions and the answer-choice table,
never in the figure, geometry, physical-parameter, or Snell-law premises.
-/
theorem problem_phyx_mini_0138
    (setup : ParallelGlassSlabSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_problem : MatchesProblemReadouts setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_geometry : SatisfiesPlaneParallelGeometry setup)
    (h_snell : SatisfiesSnellsLaw setup) :
    setup.thetaB = ((Real.pi / 3 : ℝ) : Real.Angle) ∧
      Real.Angle.sin setup.thetaB = Real.sqrt 3 / 2 ∧
      IsUniqueMatchingDisplayedSine setup .C := by
  have h_emergent :=
    emergentAngle_eq_incidentAngle setup h_physical h_problem h_geometry h_snell
  rcases h_problem with ⟨_, _, _, _, _, h_incident⟩
  have h_thetaB :
      setup.thetaB = ((Real.pi / 3 : ℝ) : Real.Angle) :=
    h_emergent.trans h_incident
  have h_sine :
      Real.Angle.sin setup.thetaB = Real.sqrt 3 / 2 := by
    rw [h_thetaB, Real.Angle.sin_coe, Real.sin_pi_div_three]
  have h_sqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    norm_num
  have h_sqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  refine ⟨h_thetaB, h_sine, ?_⟩
  refine ⟨?_, ?_⟩
  · change |Real.Angle.sin setup.thetaB - 866 / 1000| ≤ 1 / 2000
    rw [h_sine, abs_le]
    constructor <;> nlinarith
  · intro other h_other
    cases other with
    | A =>
        exfalso
        change |Real.Angle.sin setup.thetaB - 666 / 1000| ≤ 1 / 2000 at h_other
        rw [h_sine, abs_le] at h_other
        nlinarith
    | B =>
        exfalso
        change |Real.Angle.sin setup.thetaB - 966 / 1000| ≤ 1 / 2000 at h_other
        rw [h_sine, abs_le] at h_other
        nlinarith
    | C => rfl
    | D =>
        exfalso
        change |Real.Angle.sin setup.thetaB - 766 / 1000| ≤ 1 / 2000 at h_other
        rw [h_sine, abs_le] at h_other
        nlinarith

end PhyXMiniProblems.ProblemPhyXMini0138
