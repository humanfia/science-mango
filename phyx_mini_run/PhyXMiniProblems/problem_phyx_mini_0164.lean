import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Data.Set.Card
import Mathlib.Geometry.Euclidean.Projection
import Physlib.SpaceAndTime.Space.Module

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0164

/-!
# Repeated images in a triangular mirror maze

The problem describes an overhead maze whose floor is tessellated by
equilateral triangles and whose walls are mirrors.  An observer is at the
entrance labelled `x`; the monster positions are labelled `a`, `b`, and `c`.

Positions are represented by numerical SI-metre coordinates in Physlib's
two-dimensional Euclidean `Space`.  Hallway directions and ray directions are
dimensionless.  The stored image for problem 164 is not the maze described by
the problem, so this file records only the categorical geometry supplied by
the scenario and its caption; no coordinates are invented from that
mismatched image.

Assumption/target split:

* governing law: observed appearances are precisely virtual sources obtained
  by successive Euclidean reflections along clear finite-wall routes;
* previous-part results: none;
* figure/data readouts: the regular hexagonal triangular grid, the labelled
  positions and entrance arrows, wall/direction alignment, and the intended
  diagram's qualitative clear-route classification;
* current target conclusions: every visible monster has three distinct
  appearances, and that count agrees with recorded answer choice D.
-/

/-- Physlib's two-dimensional floor space, with coordinates read in metres. -/
abbrev FloorPlane : Type := Space 2

/-- Horizontal coordinate of a floor position, as a scalar metre readout. -/
def xCoordinateMeters (point : FloorPlane) : ℝ :=
  point 0

/-- Vertical coordinate of a floor position, as a scalar metre readout. -/
def yCoordinateMeters (point : FloorPlane) : ℝ :=
  point 1

/-- The three monsters named by black-dot labels in the intended figure. -/
inductive MonsterLabel where
  | a
  | b
  | c
  deriving DecidableEq, Repr, Fintype

/-- All named object and observer positions in the intended figure. -/
inductive FigurePoint where
  | entranceX
  | monsterA
  | monsterB
  | monsterC
  deriving DecidableEq, Repr, Fintype

/-- Associate each monster with its labelled black dot in the figure. -/
def figurePointOfMonster : MonsterLabel → FigurePoint
  | .a => .monsterA
  | .b => .monsterB
  | .c => .monsterC

/-- The three unoriented line families in an equilateral-triangle grid. -/
inductive HallwayDirection where
  | horizontal
  | risingDiagonal
  | fallingDiagonal
  deriving DecidableEq, Repr, Fintype

/-- The two red entrance arrows described by the intended figure caption. -/
inductive EntranceArrow where
  | upperApproach
  | sideApproach
  deriving DecidableEq, Repr, Fintype

/-- An equilateral triangular floor cell, represented by a Mathlib simplex. -/
structure TriangleCell where
  simplex : Affine.Simplex ℝ FloorPlane 2
  isEquilateral : simplex.Equilateral

/-- Advance cyclically around the six vertices of the outer hexagon. -/
def nextHexagonVertex (vertex : Fin 6) : Fin 6 :=
  vertex + 1

/-- The intended outer hexagon has six equal nonzero sides and equal radii. -/
def IsRegularHexagon
    (centerMeters : FloorPlane) (vertexMeters : Fin 6 → FloorPlane) : Prop :=
  ∃ sideLengthMeters : ℝ,
    0 < sideLengthMeters ∧
      (∀ vertex,
        dist (vertexMeters vertex) (vertexMeters (nextHexagonVertex vertex)) =
          sideLengthMeters) ∧
      ∀ vertex, dist centerMeters (vertexMeters vertex) = sideLengthMeters

/-!
A finite mirror wall has two endpoints on a one-dimensional affine supporting
line.  Reflection uses Mathlib's affine-subspace reflection, while the endpoints
retain the physically finite extent of a maze wall.
-/
structure MirrorWall where
  startMeters : FloorPlane
  endMeters : FloorPlane
  supportingLine : AffineSubspace ℝ FloorPlane
  gridDirection : HallwayDirection
  endpoints_distinct : startMeters ≠ endMeters
  start_on_supportingLine : startMeters ∈ supportingLine
  end_on_supportingLine : endMeters ∈ supportingLine
  supportingLine_is_line : Module.finrank ℝ supportingLine.direction = 1

/-- Reflect a virtual source point across a mirror wall's supporting line. -/
def reflectPointAcrossWall
    (wall : MirrorWall) (pointMeters : FloorPlane) : FloorPlane :=
  letI : Nonempty wall.supportingLine :=
    ⟨⟨wall.startMeters, wall.start_on_supportingLine⟩⟩
  EuclideanGeometry.reflection wall.supportingLine pointMeters

/-- An oriented, nonzero ray approaching the entrance. -/
structure EntranceRay where
  originMeters : FloorPlane
  direction : Space.Direction 2

/-- A ray points toward a target when positive propagation reaches it. -/
def EntranceRay.PointsToward
    (ray : EntranceRay) (targetMeters : FloorPlane) : Prop :=
  ∃ travelDistanceMeters : ℝ,
    0 < travelDistanceMeters ∧
      ray.originMeters + travelDistanceMeters • ray.direction.unit = targetMeters

/-- A candidate optical route terminating in one hallway direction family. -/
structure ReflectionRoute where
  hallwayDirection : HallwayDirection
  reflectionWalls : List MirrorWall

/-!
The physical and observational data of a maze instance.  `routeIsClear`
records occlusion and wall-segment topology; `observerSeesImageAt` records an
actual appearance.  Neither relation carries a numeric image count.
-/
structure MirrorMazeSetup where
  figurePointPositionMeters : FigurePoint → FloorPlane
  hexagonCenterMeters : FloorPlane
  hexagonVertexMeters : Fin 6 → FloorPlane
  triangleCells : Set TriangleCell
  walls : Set MirrorWall
  hallwayDirectionSubspace :
    HallwayDirection → Submodule ℝ (EuclideanSpace ℝ (Fin 2))
  entranceRay : EntranceArrow → EntranceRay
  routeIsClear : MonsterLabel → ReflectionRoute → Prop
  canonicalImagePositionMeters :
    MonsterLabel → HallwayDirection → FloorPlane
  observerSeesImageAt :
    MonsterLabel → HallwayDirection → FloorPlane → Prop

/-- Unfold a monster successively through all mirrors along a route. -/
def virtualImageFromRoute
    (setup : MirrorMazeSetup) (monster : MonsterLabel)
    (route : ReflectionRoute) : FloorPlane :=
  route.reflectionWalls.foldl
    (fun imageMeters wall => reflectPointAcrossWall wall imageMeters)
    (setup.figurePointPositionMeters (figurePointOfMonster monster))

/-- Positions at which a given monster is seen from entrance `x`. -/
def visibleImagePositions
    (setup : MirrorMazeSetup) (monster : MonsterLabel) : Set FloorPlane :=
  {imageMeters |
    ∃ direction,
      setup.observerSeesImageAt monster direction imageMeters}

/-- A monster is visible if at least one real or virtual appearance is seen. -/
def IsVisibleMonster
    (setup : MirrorMazeSetup) (monster : MonsterLabel) : Prop :=
  (visibleImagePositions setup monster).Nonempty

/-- Number of distinct appearances of a monster seen in the hallway. -/
def visibleImageCount
    (setup : MirrorMazeSetup) (monster : MonsterLabel) : ℕ :=
  (visibleImagePositions setup monster).ncard

/-!
Qualitative readouts from the intended maze figure and caption: a regular
hexagonal outline, equilateral triangular cells, three distinct one-dimensional
grid families, mirror walls aligned with those families, relative placements
of `a`, `b`, `c`, and `x`, and two distinct arrows aimed at `x`.

This predicate asserts no visibility relation and no image cardinality.
-/
def MatchesStatedMazeFigure (setup : MirrorMazeSetup) : Prop :=
  IsRegularHexagon setup.hexagonCenterMeters setup.hexagonVertexMeters ∧
    setup.triangleCells.Nonempty ∧
    setup.walls.Nonempty ∧
    (∀ direction,
      Module.finrank ℝ (setup.hallwayDirectionSubspace direction) = 1) ∧
    Function.Injective setup.hallwayDirectionSubspace ∧
    (∀ wall ∈ setup.walls,
      wall.supportingLine.direction =
        setup.hallwayDirectionSubspace wall.gridDirection) ∧
    (∀ direction,
      ∃ wall ∈ setup.walls, wall.gridDirection = direction) ∧
    setup.figurePointPositionMeters .monsterA ≠
      setup.figurePointPositionMeters .monsterB ∧
    setup.figurePointPositionMeters .monsterA ≠
      setup.figurePointPositionMeters .monsterC ∧
    setup.figurePointPositionMeters .monsterB ≠
      setup.figurePointPositionMeters .monsterC ∧
    setup.figurePointPositionMeters .entranceX ≠
      setup.figurePointPositionMeters .monsterA ∧
    setup.figurePointPositionMeters .entranceX ≠
      setup.figurePointPositionMeters .monsterB ∧
    setup.figurePointPositionMeters .entranceX ≠
      setup.figurePointPositionMeters .monsterC ∧
    xCoordinateMeters (setup.figurePointPositionMeters .monsterA) <
      xCoordinateMeters setup.hexagonCenterMeters ∧
    xCoordinateMeters (setup.figurePointPositionMeters .monsterB) =
      xCoordinateMeters setup.hexagonCenterMeters ∧
    yCoordinateMeters (setup.figurePointPositionMeters .monsterB) <
      yCoordinateMeters setup.hexagonCenterMeters ∧
    xCoordinateMeters setup.hexagonCenterMeters <
      xCoordinateMeters (setup.figurePointPositionMeters .monsterC) ∧
    yCoordinateMeters setup.hexagonCenterMeters <
      yCoordinateMeters (setup.figurePointPositionMeters .monsterC) ∧
    xCoordinateMeters (setup.figurePointPositionMeters .entranceX) <
      xCoordinateMeters setup.hexagonCenterMeters ∧
    (∀ arrow,
      (setup.entranceRay arrow).PointsToward
        (setup.figurePointPositionMeters .entranceX)) ∧
    (setup.entranceRay .upperApproach).direction ≠
      (setup.entranceRay .sideApproach).direction

/-!
The governing ideal geometrical-optics law.  An observed appearance is exactly
the virtual source obtained by successively reflecting along a clear route.
The predicate constrains neither the number of clear routes nor the number of
distinct images.
-/
structure SatisfiesIdealMirrorMazeOptics
    (setup : MirrorMazeSetup) : Prop where
  observed_iff_clear_reflection_route :
    ∀ monster direction imageMeters,
      setup.observerSeesImageAt monster direction imageMeters ↔
        ∃ route,
          setup.routeIsClear monster route ∧
            route.hallwayDirection = direction ∧
            virtualImageFromRoute setup monster route = imageMeters

/-!
Sightline data to be read from the intended maze diagram.  Clear routes use
depicted walls and unfold to a direction-indexed canonical source.  A visible
monster has a route in every grid direction, and the three canonical sources
are distinct.  These are route and position readouts, not a stated image count.
-/
structure HasFigureSightlineClassification
    (setup : MirrorMazeSetup) : Prop where
  clear_routes_use_depicted_walls :
    ∀ monster route,
      setup.routeIsClear monster route →
        ∀ wall ∈ route.reflectionWalls, wall ∈ setup.walls
  clear_route_image_is_canonical :
    ∀ monster route,
      setup.routeIsClear monster route →
        virtualImageFromRoute setup monster route =
          setup.canonicalImagePositionMeters monster route.hallwayDirection
  visible_has_clear_route_in_every_direction :
    ∀ monster,
      IsVisibleMonster setup monster →
        ∀ direction,
          ∃ route,
            setup.routeIsClear monster route ∧
              route.hallwayDirection = direction
  canonical_images_are_distinct :
    ∀ monster,
      Function.Injective (setup.canonicalImagePositionMeters monster)

/-- The three direction-indexed canonical virtual-source positions. -/
def canonicalImageSet
    (setup : MirrorMazeSetup) (monster : MonsterLabel) : Set FloorPlane :=
  Set.range (setup.canonicalImagePositionMeters monster)

/-- Ideal reflection and the intended diagram's route classification identify
the observed appearances with the canonical directional images. -/
lemma visibleImagePositions_eq_canonicalImageSet
    (setup : MirrorMazeSetup)
    (monster : MonsterLabel)
    (h_visible : IsVisibleMonster setup monster)
    (h_optics : SatisfiesIdealMirrorMazeOptics setup)
    (h_sightlines : HasFigureSightlineClassification setup) :
    visibleImagePositions setup monster = canonicalImageSet setup monster := by
  ext imageMeters
  change
    (∃ direction, setup.observerSeesImageAt monster direction imageMeters) ↔
      ∃ direction,
        setup.canonicalImagePositionMeters monster direction = imageMeters
  constructor
  · rintro ⟨direction, h_observed⟩
    rcases
        (h_optics.observed_iff_clear_reflection_route
          monster direction imageMeters).mp h_observed with
      ⟨route, h_clear, h_direction, h_image⟩
    refine ⟨direction, ?_⟩
    calc
      setup.canonicalImagePositionMeters monster direction =
          setup.canonicalImagePositionMeters monster route.hallwayDirection := by
            rw [h_direction]
      _ = virtualImageFromRoute setup monster route :=
        (h_sightlines.clear_route_image_is_canonical
          monster route h_clear).symm
      _ = imageMeters := h_image
  · rintro ⟨direction, rfl⟩
    rcases
        h_sightlines.visible_has_clear_route_in_every_direction
          monster h_visible direction with
      ⟨route, h_clear, h_direction⟩
    refine ⟨direction, ?_⟩
    apply
      (h_optics.observed_iff_clear_reflection_route
        monster direction
          (setup.canonicalImagePositionMeters monster direction)).mpr
    refine ⟨route, h_clear, h_direction, ?_⟩
    calc
      virtualImageFromRoute setup monster route =
          setup.canonicalImagePositionMeters monster route.hallwayDirection :=
        h_sightlines.clear_route_image_is_canonical monster route h_clear
      _ = setup.canonicalImagePositionMeters monster direction := by
        rw [h_direction]

/-- The injectively direction-indexed canonical image set has cardinality 3. -/
lemma canonicalImageSet_ncard
    (setup : MirrorMazeSetup)
    (monster : MonsterLabel)
    (h_sightlines : HasFigureSightlineClassification setup) :
    (canonicalImageSet setup monster).ncard = 3 := by
  rw [canonicalImageSet,
    Set.ncard_range_of_injective
      (h_sightlines.canonical_images_are_distinct monster),
    Nat.card_eq_fintype_card]
  decide

/-- Labels of the four printed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr, Fintype

/-- Appearance count printed beside each answer label in the source. -/
def answerAppearanceCount : AnswerChoice → ℕ
  | .A => 6
  | .B => 5
  | .C => 4
  | .D => 3

/-- The answer label recorded in the source dataset. -/
def recordedAnswerChoice : AnswerChoice :=
  .D

/-!
At entrance `x`, each monster that is visible has exactly three distinct
appearances in a hallway, which is recorded answer choice D.

This is the declaration corresponding to
`thm:physics:phyx_mini_0164:target`.  Neither `3` nor choice D appears in the
setup, governing optics law, figure-layout predicate, or sightline fields.
-/
theorem problem_phyx_mini_0164
    (setup : MirrorMazeSetup)
    (h_figure : MatchesStatedMazeFigure setup)
    (h_optics : SatisfiesIdealMirrorMazeOptics setup)
    (h_sightlines : HasFigureSightlineClassification setup) :
    ∀ monster,
      IsVisibleMonster setup monster →
        visibleImageCount setup monster = 3 ∧
          visibleImageCount setup monster =
            answerAppearanceCount recordedAnswerChoice := by
  intro monster h_visible
  have h_positions :
      visibleImagePositions setup monster = canonicalImageSet setup monster :=
    visibleImagePositions_eq_canonicalImageSet
      setup monster h_visible h_optics h_sightlines
  have h_count : visibleImageCount setup monster = 3 := by
    rw [visibleImageCount, h_positions]
    exact canonicalImageSet_ncard setup monster h_sightlines
  constructor
  · exact h_count
  · simpa [recordedAnswerChoice, answerAppearanceCount] using h_count

end PhyXMiniProblems.ProblemPhyXMini0164
