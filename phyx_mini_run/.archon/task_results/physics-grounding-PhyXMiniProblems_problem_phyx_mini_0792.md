# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0792.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0792.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Spatial Vector`
- `Lorentz.Vector.spatialPart` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Basic` | package PhysLean | Extract spatial components from a Lorentz vector, returning them as a vector in Euclidean space.
- `SpaceTime.space_toCoord_symm` | module `Physlib.SpaceAndTime.SpaceTime.Basic` | package PhysLean | **Spatial Component of a Spacetime Vector.** For a spacetime vector represented as a function $f: \{0\} \oplus \{0, \dots, d-1\} \to \mathbb{R}$, its spatial part is the vector in $\mathbb{R}^d$ whose $i$-th coordinat...
- `Lorentz.Vector.spatialCLM` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Basic` | package PhysLean | The spatial part of a Lorentz vector as a continuous linear map.

### Query: `Coordinate Axis`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).

### Query: `axis Index`
- `Subgroup.index` | module `Mathlib.GroupTheory.Index` | package Mathlib | The index of a subgroup as a natural number. Returns `0` if the index is infinite. [Wikidata Q1464168](https://www.wikidata.org/wiki/Q1464168)
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).
- `TensorSpecies.Tensor.indexExpr.quot` | module `Physlib.Relativity.Tensors.Elab` | package PhysLean | **Tensor Expression Index Syntax.** This defines a new syntactic category specifically for parsing and representing the indices used within tensor expressions.

### Query: `axis Vector`
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).
- `Space.toDirection` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Direction of a `Space` value with respect to the origin.

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

### Query: `Coordinate Plane`
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `LipschitzWith.coordinate` | module `Mathlib.Analysis.Normed.Lp.lpSpace` | package Mathlib | **Lipschitz Continuity of Functions into $L^\infty$.** A function $f$ from a pseudometric space into the space of bounded sequences $\ell^\infty(\iota, \mathbb{R})$ is Lipschitz continuous with constant $K$ if and onl...
- `LipschitzOnWith.coordinate` | module `Mathlib.Analysis.Normed.Lp.lpSpace` | package Mathlib | **Lipschitz Continuity of Components in $\ell^\infty$.** A function $f$ mapping from a pseudometric space to the space of bounded sequences $\ell^\infty(\iota, \mathbb{R})$ is Lipschitz continuous with constant $K$ on...

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Lorentz.Vector.spatialPart` (PhysLean)
- `SpaceTime.space_toCoord_symm` (PhysLean)
- `Lorentz.Vector.spatialCLM` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `Subgroup.index` (Mathlib)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `TensorSpecies.Tensor.indexExpr.quot` (PhysLean)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `Space.toDirection` (PhysLean)
- `Complex.I` (Mathlib)
- `iInf` (Mathlib)
- `iSup` (Mathlib)
- `WeierstrassCurve.j` (Mathlib)
- `Matrix.crossProductMatrix_crossProductVee` (PhysLean)
- `Matrix.J` (Mathlib)
- `Turing.PartrecToTM2.K'` (Mathlib)
- `Turing.PartrecToTM2.K'.elim` (Mathlib)
- `Constants.kB` (PhysLean)
- `UpperHalfPlane` (Mathlib)
- `LipschitzWith.coordinate` (Mathlib)
- `LipschitzOnWith.coordinate` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0792.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0792.AxisSense`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0792.CoordinateAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0792.CoordinatePlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0792.FigureVectorLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0792.LiesInCoordinatePlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0792.MatchesSuppliedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0792.PointsAlongPositiveAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0792.SatisfiesVectorProductLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0792.SpatialVector`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0792.StatedVectorData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0792.VectorProductFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0792.VectorProductSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
