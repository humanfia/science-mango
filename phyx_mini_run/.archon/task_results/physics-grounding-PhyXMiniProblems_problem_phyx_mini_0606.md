# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0606.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0606.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:f0369c0cf666c7700f12ff01a6ae32d44cda30a59ff3830702f3a98d11d266c9
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Triangle Site`
- `CategoryTheory.Pretriangulated.Triangle` | module `Mathlib.CategoryTheory.Triangulated.Basic` | package Mathlib | A triangle in `C` is a sextuple `(X,Y,Z,f,g,h)` where `X,Y,Z` are objects of `C`, and `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ X⟦1⟧` are morphisms in `C`.
- `dist_triangle` | module `Mathlib.Topology.MetricSpace.Pseudo.Defs` | package Mathlib | **Triangle Inequality.** In a pseudometric space, the distance between any two points $x$ and $z$ is less than or equal to the sum of the distance from $x$ to $y$ and the distance from $y$ to $z$.
- `Affine.Triangle.toPolygon_vertices` | module `Mathlib.Geometry.Polygon.Basic` | package Mathlib | **Vertices of a Triangle as a Polygon.** For any triangle in an affine space, the vertices of its representation as a polygon are identical to the three points that define the triangle.

### Query: `Triangle Figure Position`
- `CategoryTheory.Pretriangulated.Triangle` | module `Mathlib.CategoryTheory.Triangulated.Basic` | package Mathlib | A triangle in `C` is a sextuple `(X,Y,Z,f,g,h)` where `X,Y,Z` are objects of `C`, and `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ X⟦1⟧` are morphisms in `C`.
- `Mathlib.Tactic.Widget.subTriangle` | module `Mathlib.Tactic.Widget.CommDiag` | package Mathlib | Triangle with `homs = [f,g,h]` and `objs = [A,B,C]` ``` A f B h g C ```
- `CategoryTheory.Pretriangulated.Triangle.mk_mor₃` | module `Mathlib.CategoryTheory.Triangulated.Basic` | package Mathlib | **Construction of a Triangle.** Given objects $X, Y, Z$ in a category $C$ equipped with a shift functor, and morphisms $f: X \to Y$, $g: Y \to Z$, and $h: Z \to X[1]$, we can define a triangle in $C$ whose first, seco...

### Query: `Vertical Spin Arrow`
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.
- `CategoryTheory.Arrow` | module `Mathlib.CategoryTheory.Comma.Arrow` | package Mathlib | The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative squares in `T`.
- `CategoryTheory.TwoSquare.«term𝟙ᵥ»` | module `Mathlib.CategoryTheory.Functor.TwoSquare` | package Mathlib | Notation for the vertical identity 2-square.

### Query: `Spin Triangle Figure`
- `CategoryTheory.Pretriangulated.Triangle` | module `Mathlib.CategoryTheory.Triangulated.Basic` | package Mathlib | A triangle in `C` is a sextuple `(X,Y,Z,f,g,h)` where `X,Y,Z` are objects of `C`, and `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ X⟦1⟧` are morphisms in `C`.
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.
- `Mathlib.Tactic.Widget.subTriangle` | module `Mathlib.Tactic.Widget.CommDiag` | package Mathlib | Triangle with `homs = [f,g,h]` and `objs = [A,B,C]` ``` A f B h g C ```

### Query: `Matches Supplied Spin Triangle Figure`
- `CategoryTheory.Pretriangulated.Triangle` | module `Mathlib.CategoryTheory.Triangulated.Basic` | package Mathlib | A triangle in `C` is a sextuple `(X,Y,Z,f,g,h)` where `X,Y,Z` are objects of `C`, and `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ X⟦1⟧` are morphisms in `C`.
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.
- `CategoryTheory.Pretriangulated.productTriangle.fan` | module `Mathlib.CategoryTheory.Triangulated.Basic` | package Mathlib | The fan given by `productTriangle T`.

### Query: `Three Spin Basis`
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.
- `Module.Basis` | module `Mathlib.LinearAlgebra.Basis.Defs` | package Mathlib | A `Basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`. The basis vectors are available as `DFunLike.coe (b : Basis ι R M) : ι → M`. To turn a linear independent family of vectors spanning `M` in...
- `GroupTheory.SO3.exists_basis_preserved` | module `Physlib.Mathematics.SO3.Basic` | package PhysLean | For every element of `SO(3)` there exists a basis indexed by `Fin 3` under which the first element remains invariant.

### Query: `Three Spin State`
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.
- `ThreeAPFree` | module `Mathlib.Combinatorics.Additive.AP.Three.Defs` | package Mathlib | A set is **3AP-free** if it does not contain any non-trivial arithmetic progression of length three. This is also sometimes called a **non-averaging set** or **Salem-Spencer set**.
- `ThreeGPFree` | module `Mathlib.Combinatorics.Additive.AP.Three.Defs` | package Mathlib | A set is **3GP-free** if it does not contain any non-trivial geometric progression of length three.

### Query: `Spin Axis`
- `spinGroup.star_mem_iff` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | An element is in `spinGroup Q` if and only if `star x` is in `spinGroup Q`. See `star_mem` for only one direction.
- `Orientation.rotation` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | A rotation by the oriented angle `θ`.
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.

### Query: `to Fin3`
- `WeierstrassCurve.Jacobian.smul_fin3` | module `Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Basic` | package Mathlib | **Scalar Multiplication of Jacobian Coordinates.** For a point $P = (x, y, z)$ in Jacobian coordinates represented as a 3-tuple over a commutative ring $R$, and a scalar $u \in R$, the scalar action of $u$ on $P$ is d...
- `Set.Finite.toFinset` | module `Mathlib.Data.Set.Finite.Basic` | package Mathlib | Using choice, get the `Finset` that represents this `Set`.
- `WeierstrassCurve.Jacobian.fin3_def` | module `Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Basic` | package Mathlib | **Vector Representation in Dimension Three.** For any function $P$ mapping the set $\{0, 1, 2\}$ to a ring $R$, the vector formed by the components $P(0)$, $P(1)$, and $P(2)$ is equal to $P$ itself.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `CategoryTheory.Pretriangulated.Triangle` (Mathlib)
- `dist_triangle` (Mathlib)
- `Affine.Triangle.toPolygon_vertices` (Mathlib)
- `CategoryTheory.Pretriangulated.Triangle` (Mathlib)
- `Mathlib.Tactic.Widget.subTriangle` (Mathlib)
- `CategoryTheory.Pretriangulated.Triangle.mk_mor₃` (Mathlib)
- `spinGroup` (Mathlib)
- `CategoryTheory.Arrow` (Mathlib)
- `CategoryTheory.TwoSquare.«term𝟙ᵥ»` (Mathlib)
- `CategoryTheory.Pretriangulated.Triangle` (Mathlib)
- `spinGroup` (Mathlib)
- `Mathlib.Tactic.Widget.subTriangle` (Mathlib)
- `CategoryTheory.Pretriangulated.Triangle` (Mathlib)
- `spinGroup` (Mathlib)
- `CategoryTheory.Pretriangulated.productTriangle.fan` (Mathlib)
- `spinGroup` (Mathlib)
- `Module.Basis` (Mathlib)
- `GroupTheory.SO3.exists_basis_preserved` (PhysLean)
- `spinGroup` (Mathlib)
- `ThreeAPFree` (Mathlib)
- `ThreeGPFree` (Mathlib)
- `spinGroup.star_mem_iff` (Mathlib)
- `Orientation.rotation` (Mathlib)
- `spinGroup` (Mathlib)
- `WeierstrassCurve.Jacobian.smul_fin3` (Mathlib)
- `Set.Finite.toFinset` (Mathlib)
- `WeierstrassCurve.Jacobian.fin3_def` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0606.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.HasAntiferromagneticExchange`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.HasEnergyEigenvalue`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.IsGroundStateEnergy`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.MatchesSuppliedSpinTriangleFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.SatisfiesTriangularHeisenbergHamiltonian`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.SpinAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.SpinHalfTriangleExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.SpinTriangleFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.ThreeSpinBasis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.ThreeSpinState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.TriangleFigurePosition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.TriangleSite`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0606.VerticalSpinArrow`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
