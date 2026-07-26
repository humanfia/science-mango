# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0733.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0733.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:74bf5e9c2bc6bbef2efec33396f7faa504cd1b024379077cce83f5a0cb2ae300
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `angle From Degrees`
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `Real.Angle.coe_two_pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **The Angle of $2\pi$.** The real number $2\pi$, when considered as an angle, is equal to the zero angle.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)

### Query: `Moving Body Kind`
- `Turing.TM0.Stmt.move` | module `Mathlib.Computability.TuringMachine.PostTuringMachine` | package Mathlib | **Turing Machine Movement Statement.** The instruction `move` is a type of Turing machine statement that directs the tape head to move in a specified direction (either left or right).
- `RigidBody.center_of_mass_point_moves_as_particle` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | The centre of mass of a rigid body moves as if all mass were concentrated at that point and acted upon by the resultant external force: M a_CM = ∑ F_ext.
- `RigidBodyMotion` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | A motion of a rigid body in `d`-dimensional space: the body together with the inertial-frame trajectory of its centre of mass and its time-dependent orientation (a rotation about the centre of mass).

### Query: `Support Surface Kind`
- `Function.support` | module `Mathlib.Algebra.Notation.Support` | package Mathlib | `support` of a function is the set of points `x` such that `f x ≠ 0`.
- `Finsupp.splitSupport` | module `Mathlib.Data.Finsupp.Basic` | package Mathlib | Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `β`, `split_support l` is the finset of indices in `ι` that appear in the support of `l`.
- `Finsupp.sigma_support` | module `Mathlib.Data.Finsupp.Basic` | package Mathlib | **Support of a Finitely Supported Function on a Sigma Type.** The support of a finitely supported function $l$ defined on a sigma type $\sum_{i \in \iota} \alpha_i$ is equal to the disjoint union (sigma product) of th...

### Query: `Along Plank Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `AffineSubspace.mem_direction_iff_eq_vsub` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | A vector is in the direction of a nonempty affine subspace if and only if it is the subtraction of two vectors in the subspace.

### Query: `Figure Object`
- `CategoryTheory.ObjectProperty` | module `Mathlib.CategoryTheory.ObjectProperty.Basic` | package Mathlib | A property of objects in a category `C` is a predicate `C → Prop`.
- `Concept.ofObject` | module `Mathlib.Order.Concept` | package Mathlib | The concept generated by a single object.
- `CategoryTheory.Functor.obj_mem_essImage` | module `Mathlib.CategoryTheory.EssentialImage` | package Mathlib | An object in the image is in the essential image.

### Query: `Figure Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel'` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Lifting Labels to the Writer Monad Transformer.** Given a monoid $\omega$, a label for a computation in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be transformed into a label for a computa...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `EuclideanGeometry.angle` (Mathlib)
- `Real.Angle.coe_two_pi` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Turing.TM0.Stmt.move` (Mathlib)
- `RigidBody.center_of_mass_point_moves_as_particle` (PhysLean)
- `RigidBodyMotion` (PhysLean)
- `Function.support` (Mathlib)
- `Finsupp.splitSupport` (Mathlib)
- `Finsupp.sigma_support` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `AffineSubspace.mem_direction_iff_eq_vsub` (Mathlib)
- `CategoryTheory.ObjectProperty` (Mathlib)
- `Concept.ofObject` (Mathlib)
- `CategoryTheory.Functor.obj_mem_essImage` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel'` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0733.AlongPlankDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.FigureObject`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.HasPhysicalMachineryInclineParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.IsUniqueRoundedAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.MachineryInclineSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.MatchesMachineryInclineReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.MatchesMachineryInclineScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.MatchesSuppliedInclinedPlankFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.MovingBodyKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.RoundsToDisplayedHundredth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.SatisfiesInclinedPlankProjectionLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.SuppliedInclinedPlankFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0733.SupportSurfaceKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
