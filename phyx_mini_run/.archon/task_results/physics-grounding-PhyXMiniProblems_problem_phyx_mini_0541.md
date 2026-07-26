# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0541.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0541.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:9af7e3165548e40358694b64bb8998924d1859989a6bb773321ec1de64e7e5bc
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `EuclideanSpace vector components`
- `EuclideanSpace` | module `Mathlib.Analysis.InnerProductSpace.PiL2` | package Mathlib | The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space use `EuclideanSpace 𝕜 (Fin n)`. For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building element...
- `Space.fderiv_space_components` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | **Components of the Fréchet Derivative of a Vector-Valued Function.** For a differentiable function $f$ mapping from a normed space $M$ to the space of $d$-dimensional vectors $\mathbb{R}^d$, the $\mu$-th component of...
- `Lorentz.ContrMod.toSpace` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Modules` | package PhysLean | The underlying space part of a `ContrMod` formed by removing the first element. A better name for this might be `tail`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Spin Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.

### Query: `Spin Outcome`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `spinGroup.mem_even` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | **Elements of the Spin Group are Even.** Every element of the spin group associated with a quadratic form $Q$ is contained within the even subalgebra of the corresponding Clifford algebra.
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.

### Query: `outcome Sign`
- `SignType.sign` | module `Mathlib.Data.Sign.Defs` | package Mathlib | The sign of an element is 1 if it's positive, -1 if negative, 0 otherwise.
- `Ordering.Compares.eq_eq` | module `Mathlib.Order.Compare` | package Mathlib | **Equality Characterization of Comparison Outcomes.** In a preorder, if a comparison outcome $o$ holds between two elements $a$ and $b$, then $o$ is the equality outcome if and only if $a$ is equal to $b$.
- `SignType` | module `Mathlib.Data.Sign.Defs` | package Mathlib | The type of signs.

### Query: `spin Direction Dot`
- `dotProduct` | module `Mathlib.Data.Matrix.Mul` | package Mathlib | `dotProduct v w` is the sum of the entrywise products `v i * w i`. See also `dotProductEquiv`.
- `direction_affineSpan` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of the affine span is the `vectorSpan`.
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.

### Query: `spherical Spin Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `EuclideanGeometry.Sphere.direction_orthRadius` | module `Mathlib.Geometry.Euclidean.Sphere.OrthRadius` | package Mathlib | **Direction of the Orthogonal Subspace to the Radius.** For any sphere $s$ and any point $p$, the direction of the affine subspace orthogonal to the radius at $p$ is the orthogonal complement of the one-dimensional su...
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.

### Query: `positive XDirection`
- `IsStrictlyPositive` | module `Mathlib.Algebra.Algebra.StrictPositivity` | package Mathlib | An element of an ordered algebra is *strictly positive* if it is nonnegative and invertible. NOTE: This definition will be generalized to the non-unital case in the future; do not unfold the definition and use the API...
- `LSeries.positive` | module `Mathlib.NumberTheory.LSeries.Positivity` | package Mathlib | If all values of `a : ℕ → ℂ` are nonnegative reals and `a 1` is positive, then `L a x` is positive real for all real `x` larger than `abscissaOfAbsConv a`.
- `EuclideanGeometry.o` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | A fixed choice of positive orientation of Euclidean space `ℝ²`

### Query: `Analyzer Angle Readouts`
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `Real.Angle` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | The type of angles
- `Orientation.oangle_sub_left_smul_rotation_pi_div_two` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle` | package Mathlib | An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple of a rotation of another by `π / 2`, version subtracting vectors.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `spinGroup` (Mathlib)
- `Space.Direction` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `spinGroup.mem_even` (Mathlib)
- `spinGroup` (Mathlib)
- `SignType.sign` (Mathlib)
- `Ordering.Compares.eq_eq` (Mathlib)
- `SignType` (Mathlib)
- `dotProduct` (Mathlib)
- `direction_affineSpan` (Mathlib)
- `spinGroup` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `EuclideanGeometry.Sphere.direction_orthRadius` (Mathlib)
- `spinGroup` (Mathlib)
- `IsStrictlyPositive` (Mathlib)
- `LSeries.positive` (Mathlib)
- `EuclideanGeometry.o` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `Real.Angle` (Mathlib)
- `Orientation.oangle_sub_left_smul_rotation_pi_div_two` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0541.AnalyzerAngleReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.IsUniqueMatchingAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.MatchesDisplayedChoiceWithin`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.MatchesSternGerlachQuestion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.MatchesSuppliedRelativityRaster`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.PointsAlongPositiveHorizontalAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.ProbabilityApproximatelyEqual`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.RasterAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.RasterFrame`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.RasterObject`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.RasterVelocitySymbol`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.SatisfiesSequentialAnalyzerSemantics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.SatisfiesSpinHalfBornRule`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.SequentialSternGerlachExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.SpinDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.SpinHalfTransitionModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.SpinOutcome`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0541.SuppliedRelativityRaster`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
