# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0164.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0164.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:b2508e84434ce11e37838e7e2489b2fc2d8d86a3c48725be5dadc6326db0f75f
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Floor Plane`
- `Int.floor` | module `Mathlib.Algebra.Order.Floor.Defs` | package Mathlib | `Int.floor a` is the greatest integer `z` such that `z ≤ a`. It is denoted with `⌊a⌋`.
- `Int.floor_int` | module `Mathlib.Algebra.Order.Floor.Defs` | package Mathlib | **Floor of an Integer.** The floor function restricted to the integers is the identity function; that is, for any integer $n$, $\lfloor n \rfloor = n$.
- `Nat.floor` | module `Mathlib.Algebra.Order.Floor.Defs` | package Mathlib | `⌊a⌋₊` is the greatest natural `n` such that `n ≤ a`. If `a` is negative, then `⌊a⌋₊ = 0`.

### Query: `x Coordinate Meters`
- `Polynomial.X` | module `Mathlib.Algebra.Polynomial.Basic` | package Mathlib | `X` is the polynomial variable (aka indeterminate).
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LipschitzWith.coordinate` | module `Mathlib.Analysis.Normed.Lp.lpSpace` | package Mathlib | **Lipschitz Continuity of Functions into $L^\infty$.** A function $f$ from a pseudometric space into the space of bounded sequences $\ell^\infty(\iota, \mathbb{R})$ is Lipschitz continuous with constant $K$ if and onl...

### Query: `y Coordinate Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `WeierstrassCurve.Projective.negY` | module `Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula` | package Mathlib | The `Y`-coordinate of a representative of `-P` for a projective point representative `P` on a Weierstrass curve.
- `LengthUnit.yards` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a yard (0.9144 meters)

### Query: `Monster Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `StateT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **State Monad Transformer Label Mapping.** Given a continuation label that maps a pair consisting of a value and a state to a computation in a base monad, this construction defines a corresponding label for the state...
- `WriterT.mkLabel'` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Lifting Labels to the Writer Monad Transformer.** Given a monoid $\omega$, a label for a computation in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be transformed into a label for a computa...

### Query: `Figure Point`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `figure Point Of Monster`
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`
- `CategoryTheory.GrothendieckTopology.Point` | module `Mathlib.CategoryTheory.Sites.Point.Basic` | package Mathlib | Given `J` a Grothendieck topology on a category `C`, a point of the site `(C, J)` consists of a functor `fiber : C ⥤ Type w` such that the category `fiber.Elements` is initially small (which allows defining the fiber...
- `Locale.localePointOfSpacePoint` | module `Mathlib.Topology.Order.Category.FrameAdjunction` | package Mathlib | The unit of the adjunction between locales and topological spaces, which associates with a point `x` of the space `X` a point of the locale of opens of `X`.

### Query: `Hallway Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `Turing.Dir.left` | module `Mathlib.Computability.TuringMachine.Tape` | package Mathlib | **Left Direction.** One of the two possible directions of movement for a Turing machine head.

### Query: `Entrance Arrow`
- `arrowAction` | module `Mathlib.Algebra.Group.Action.Basic` | package Mathlib | If `G` acts on `A`, then it acts also on `A → B`, by `(g • F) a = F (g⁻¹ • a)`.
- `CategoryTheory.StructuredArrow` | module `Mathlib.CategoryTheory.Comma.StructuredArrow.Basic` | package Mathlib | The category of `T`-structured arrows with domain `S : D` (here `T : C ⥤ D`), has as its objects `D`-morphisms of the form `S ⟶ T Y`, for some `Y : C`, and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle...
- `CategoryTheory.Arrow.Hom.right` | module `Mathlib.CategoryTheory.Comma.Arrow` | package Mathlib | The right part of a morphism in the category of arrows.

### Query: `Triangle Cell`
- `CategoryTheory.Pretriangulated.Triangle` | module `Mathlib.CategoryTheory.Triangulated.Basic` | package Mathlib | A triangle in `C` is a sextuple `(X,Y,Z,f,g,h)` where `X,Y,Z` are objects of `C`, and `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ X⟦1⟧` are morphisms in `C`.
- `CategoryTheory.Triangulated.Octahedron'.triangle_obj₁` | module `Mathlib.CategoryTheory.Triangulated.Triangulated` | package Mathlib | **The Third Triangle of an Octahedron.** In a triangulated category, given an octahedron, the third associated triangle is the triangle object consisting of the sequence of morphisms $Z_{12} \xrightarrow{m_1} Z_{13} \...
- `CategoryTheory.Triangulated.Octahedron'.triangle_obj₂` | module `Mathlib.CategoryTheory.Triangulated.Triangulated` | package Mathlib | **The Third Triangle of an Octahedron.** In a triangulated category, given an octahedron, the third associated triangle is the triangle consisting of the objects $Z_{12}$, $Z_{13}$, and $Z_{23}$, along with the morphi...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Int.floor` (Mathlib)
- `Int.floor_int` (Mathlib)
- `Nat.floor` (Mathlib)
- `Polynomial.X` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LipschitzWith.coordinate` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `WeierstrassCurve.Projective.negY` (Mathlib)
- `LengthUnit.yards` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `StateT.mkLabel` (Mathlib)
- `WriterT.mkLabel'` (Mathlib)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `OnePoint` (Mathlib)
- `CategoryTheory.GrothendieckTopology.Point` (Mathlib)
- `Locale.localePointOfSpacePoint` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `Turing.Dir.left` (Mathlib)
- `arrowAction` (Mathlib)
- `CategoryTheory.StructuredArrow` (Mathlib)
- `CategoryTheory.Arrow.Hom.right` (Mathlib)
- `CategoryTheory.Pretriangulated.Triangle` (Mathlib)
- `CategoryTheory.Triangulated.Octahedron'.triangle_obj₁` (Mathlib)
- `CategoryTheory.Triangulated.Octahedron'.triangle_obj₂` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0164.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.EntranceArrow`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.EntranceRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.EntranceRay.PointsToward`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.FloorPlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.HallwayDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.HasFigureSightlineClassification`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.IsRegularHexagon`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.IsVisibleMonster`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.MatchesStatedMazeFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.MirrorMazeSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.MirrorWall`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.MonsterLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.ReflectionRoute`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.SatisfiesIdealMirrorMazeOptics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0164.TriangleCell`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
