# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0682.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0682.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:ba0f90140b97309d6eed1ab6b2d2f2d6ee861f3d59b9ee8b838f9ea1eaf67ec1
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

### Query: `Spatial Displacement`
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `GalileanGroup.ofSpaceTranslation_spaceTranslation` | module `Physlib.SpaceAndTime.GalileanGroup.Basic` | package PhysLean | **Spatial Translation Component of a Pure Spatial Translation.** For any vector $a$ in $d$-dimensional Euclidean space, the spatial translation component of the Galilean transformation defined by the pure spatial tran...

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `displacement Readout`
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBodyMotion.displacement_apply` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The `k`-th coordinate of the rigid displacement applied to `y`.

### Query: `i Hat`
- `Complex.I` | module `Mathlib.Data.Complex.Basic` | package Mathlib | The imaginary unit.
- `iInf` | module `Mathlib.Order.SetNotation` | package Mathlib | Indexed infimum
- `iSup` | module `Mathlib.Order.SetNotation` | package Mathlib | Indexed supremum

### Query: `j Hat`
- `WeierstrassCurve.j` | module `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass` | package Mathlib | The j-invariant `j` of an elliptic curve, which is invariant under isomorphisms over `R`. Note that to prove two equal elliptic curves have the same `j`, you need to use `simp_rw`, as `rw` cannot transfer instance `We...
- `Matrix.crossProductMatrix_crossProductVee` | module `Physlib.Mathematics.CrossProductMatrix` | package PhysLean | On skew-symmetric matrices the hat map is also a right inverse of the vee map: if `Aᵀ = -A` then `[Aᵛ]ₓ = A`. Together with `crossProductVee_crossProductMatrix` this identifies `ℝ³` with the skew-symmetric `3 × 3` mat...
- `Matrix.J` | module `Mathlib.LinearAlgebra.SymplecticGroup` | package Mathlib | The matrix defining the canonical skew-symmetric bilinear form.

### Query: `k Hat`
- `Turing.PartrecToTM2.K'` | module `Mathlib.Computability.TuringMachine.ToPartrec` | package Mathlib | The four stacks used by the program. `main` is used to store the input value in `trNormal` mode and the output value in `Λ'.ret` mode, while `stack` is used to keep all the data for the continuations. `rev` is used to...
- `Turing.PartrecToTM2.K'.elim` | module `Mathlib.Computability.TuringMachine.ToPartrec` | package Mathlib | This is the nondependent eliminator for `K'`, but we use it specifically here in order to represent the stack data as four lists rather than as a function `K' → List Γ'`, because this makes rewrites easier. The theore...
- `Constants.kB` | module `Physlib.StatisticalMechanics.BoltzmannConstant` | package PhysLean | The Boltzmann constant in a given but arbitrary set of units. Boltzman's constant has dimension equivalent to `Energy/Temperature`.

### Query: `Coordinate Axis`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).

### Query: `Dimension Label`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `Order.krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | The **Krull dimension** of a preorder `α` is the supremum of the rightmost index of all relation series of `α` ordered by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull dimension is defined to...
- `HasDim` | module `Physlib.Units.Basic` | package PhysLean | This typeclass indicates that there is a dimension `dim M : Dimension` associated with the type `M`.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `RigidBodyMotion.displacement` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `GalileanGroup.ofSpaceTranslation_spaceTranslation` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `RigidBodyMotion.displacement` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBodyMotion.displacement_apply` (PhysLean)
- `Complex.I` (Mathlib)
- `iInf` (Mathlib)
- `iSup` (Mathlib)
- `WeierstrassCurve.j` (Mathlib)
- `Matrix.crossProductMatrix_crossProductVee` (PhysLean)
- `Matrix.J` (Mathlib)
- `Turing.PartrecToTM2.K'` (Mathlib)
- `Turing.PartrecToTM2.K'.elim` (Mathlib)
- `Constants.kB` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `Dimension` (PhysLean)
- `Order.krullDim` (Mathlib)
- `HasDim` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0682.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.CoordinateAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.DimensionLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.FigurePointLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.FigureVectorLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.HasPositiveEdgeLengths`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.MatchesDisplayedBodyDiagonal`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.MatchesSuppliedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.RectangularParallelepipedSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.SatisfiesBaseFaceDiagonalGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.SatisfiesBodyDiagonalRightTriangle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.SpatialDisplacement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.SuppliedParallelepipedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0682.VectorRole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
