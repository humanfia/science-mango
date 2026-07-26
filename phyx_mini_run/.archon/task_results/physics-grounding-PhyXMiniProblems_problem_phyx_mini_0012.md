# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0012.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0012.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:849e2c97c4f32d5e2692eb71acc5c8abd9b3da4351c665d3188bff42329c2092
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Fiber Length`
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `FiberBundle` | module `Mathlib.Topology.FiberBundle.Basic` | package Mathlib | A (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on `B` for which the fibers are all homeomorphic to `F`, such that the local situation around each point is a direct product.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Bent Optical Fiber`
- `FiberBundle` | module `Mathlib.Topology.FiberBundle.Basic` | package Mathlib | A (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on `B` for which the fibers are all homeomorphic to `F`, such that the local situation around each point is a direct product.
- `FiberBundle.trivializationAt` | module `Mathlib.Topology.FiberBundle.Basic` | package Mathlib | Trivialization of a fiber bundle at a point.
- `CategoryTheory.Limits.BinaryBicone.op_snd` | module `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts` | package Mathlib | **Opposite of the Second Projection of a Binary Bicone.** For a binary bicone $b$ between objects $P$ and $Q$, the second projection of its opposite bicone $b^{op}$ is the morphism in the opposite category correspondi...

### Query: `Axial Ray Confinement Model`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.

### Query: `minimum outside radius`
- `List.minimum` | module `Mathlib.Data.List.MinMax` | package Mathlib | `minimum l` returns a `WithTop α`, the smallest element of `l` for nonempty lists, and `⊤` for `[]`
- `FormalMultilinearSeries.radius` | module `Mathlib.Analysis.Analytic.ConvergenceRadius` | package Mathlib | The radius of a formal multilinear series is the largest `r` such that the sum `Σ ‖pₙ‖ ‖y‖ⁿ` converges for all `‖y‖ < r`. This implies that `Σ pₙ yⁿ` converges for all `‖y‖ < r`, but these definitions are *not* equiva...
- `SmoothBumpFunction.rOut_pos` | module `Mathlib.Geometry.Manifold.BumpFunction` | package Mathlib | **Positivity of the Outer Radius.** For any smooth bump function $f$, the outer radius $r_{out}$ is strictly positive.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `FiberBundle` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `FiberBundle` (Mathlib)
- `FiberBundle.trivializationAt` (Mathlib)
- `CategoryTheory.Limits.BinaryBicone.op_snd` (Mathlib)
- `SameRay` (Mathlib)
- `Module.Ray` (Mathlib)
- `RayVector` (Mathlib)
- `List.minimum` (Mathlib)
- `FormalMultilinearSeries.radius` (Mathlib)
- `SmoothBumpFunction.rOut_pos` (Mathlib)

## Local abstractions introduced

- `PhyXMini0012.AxialRayConfinementModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0012.BentOpticalFiber`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0012.FiberLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
