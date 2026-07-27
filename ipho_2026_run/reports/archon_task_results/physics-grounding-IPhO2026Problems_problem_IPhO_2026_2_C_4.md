# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_2_C_4.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_4.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:95865acb046df62010ceb83d3e662e31b3408e215495a08e357844bca2877a23
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `LengthReading`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `CubeRootLengthReading`
- `RootPairing.RootPositiveForm.rootLength` | module `Mathlib.LinearAlgebra.RootSystem.RootPositive` | package Mathlib | The length of the `i`-th root w.r.t. a root-positive form taking values in `S`.
- `UpperHalfPlane.norm_ρ` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | **Norm of the Cube Root of Unity.** The complex norm of the primitive cube root of unity $\rho = -\frac{1}{2} + i\frac{\sqrt{3}}{2}$ is equal to $1$.
- `RootPairing.RootPositiveForm.rootLength_pos` | module `Mathlib.LinearAlgebra.RootSystem.RootPositive` | package Mathlib | **Positivity of Root Lengths.** For any index $i$ in the indexing set of a root pairing, the squared length of the associated root, as determined by the root positive form, is strictly positive.

### Query: `ReflectedLineReadout`
- `AffineMap.lineMap` | module `Mathlib.LinearAlgebra.AffineSpace.AffineMap` | package Mathlib | The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`.
- `lineDeriv` | module `Mathlib.Analysis.Calculus.LineDeriv.Basic` | package Mathlib | Line derivative of `f` at the point `x` in the direction `v`, if it exists. Zero otherwise. If the line derivative exists (i.e., `∃ f', HasLineDerivAt 𝕜 f f' x v`), then `f (x + t v) = f x + t lineDeriv 𝕜 f x v + o (t...
- `«termLine[_,_,_]»` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The line between two points, as an affine subspace.

### Query: `Figure2gOpticalSystem`
- `IsPiSystem` | module `Mathlib.MeasureTheory.PiSystem` | package Mathlib | A π-system is a collection of subsets of `α` that is closed under binary intersection of non-disjoint sets. Usually it is also required that the collection is nonempty, but we don't do that here.
- `CoxeterSystem` | module `Mathlib.GroupTheory.Coxeter.Basic` | package Mathlib | A Coxeter system `CoxeterSystem M W` is a structure recording the isomorphism between a group `W` and the Coxeter group associated to a Coxeter matrix `M`.
- `Function.Pullback.snd` | module `Mathlib.Data.Set.Prod` | package Mathlib | The projection from the fiber product to the second factor.

### Query: `neighboringIntersectionX`
- `Polynomial.X` | module `Mathlib.Algebra.Polynomial.Basic` | package Mathlib | `X` is the polynomial variable (aka indeterminate).
- `inter_mem_nhdsWithin_inter` | module `Mathlib.Topology.NhdsWithin` | package Mathlib | **Intersection of Neighborhoods within Intersecting Sets.** Let $x$ be a point in a topological space. If $a$ is a neighborhood of $x$ within the set $b$, and $c$ is a neighborhood of $x$ within the set $d$, then the...
- `mem_nhdsWithin_self_inter` | module `Mathlib.Topology.NhdsWithin` | package Mathlib | **Membership in the Neighborhood Filter within an Intersection.** For any point $x$ and any subsets $s$ and $t$ of a topological space, the set $s$ is a neighborhood of $x$ within the intersection $s \cap t$.

### Query: `neighboringIntersectionY`
- `Pell.Solution₁.y` | module `Mathlib.NumberTheory.Pell` | package Mathlib | The `y` component of a solution to the Pell equation `x^2 - d*y^2 = 1`
- `WeierstrassCurve.Projective.negY` | module `Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula` | package Mathlib | The `Y`-coordinate of a representative of `-P` for a projective point representative `P` on a Weierstrass curve.
- `nhdsKer_iInter_subset` | module `Mathlib.Topology.NhdsKer` | package Mathlib | **Neighborhood Kernel of an Intersection.** The neighborhood kernel of the intersection of a family of sets is a subset of the intersection of the neighborhood kernels of each individual set in that family.

### Query: `NeighboringReflectedRaysGenerateCaustic`
- `Filter.generate` | module `Mathlib.Order.Filter.Basic` | package Mathlib | `generate g` is the largest filter containing the sets `g`.
- `MeasurableSpace.generateFrom` | module `Mathlib.MeasureTheory.MeasurableSpace.Defs` | package Mathlib | Construct the smallest measure space containing a collection of basic sets
- `EuclideanGeometry.oangle_pointReflection_right` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | **Oriented Angle under Point Reflection of the Second Ray.** For any three points $p_1, p_2, p_3$ in a Euclidean geometry such that $p_1 \neq p_2$ and $p_3 \neq p_2$, the oriented angle $\measuredangle p_1 p_2 p_3'$ f...

### Query: `HasPreviousPartC3Coordinates`
- `Part` | module `Mathlib.Data.Part` | package Mathlib | `Part α` is the type of "partial values" of type `α`. It is similar to `Option α` except the domain condition can be an arbitrary proposition, not necessarily decidable.
- `Part.hasFix` | module `Mathlib.Control.Fix` | package Mathlib | **Fixed-Point Operator for Partial Values.** The type of partial values of type $\alpha$ admits a fixed-point operator, where the fixed point of a function $f$ is defined by applying the underlying partial fixed-point...
- `ComplexShape.prev_eq'` | module `Mathlib.Algebra.Homology.ComplexShape` | package Mathlib | **Previous Index of a Related Pair.** For a complex shape $c$ and indices $i, j$, if $i$ is related to $j$ in $c$, then the previous index of $j$ is equal to $i$.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Reading`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

## Grounded Mathlib/PhysLean names

- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `RootPairing.RootPositiveForm.rootLength` (Mathlib)
- `UpperHalfPlane.norm_ρ` (Mathlib)
- `RootPairing.RootPositiveForm.rootLength_pos` (Mathlib)
- `AffineMap.lineMap` (Mathlib)
- `lineDeriv` (Mathlib)
- `«termLine[_,_,_]»` (Mathlib)
- `IsPiSystem` (Mathlib)
- `CoxeterSystem` (Mathlib)
- `Function.Pullback.snd` (Mathlib)
- `Polynomial.X` (Mathlib)
- `inter_mem_nhdsWithin_inter` (Mathlib)
- `mem_nhdsWithin_self_inter` (Mathlib)
- `Pell.Solution₁.y` (Mathlib)
- `WeierstrassCurve.Projective.negY` (Mathlib)
- `nhdsKer_iInter_subset` (Mathlib)
- `Filter.generate` (Mathlib)
- `MeasurableSpace.generateFrom` (Mathlib)
- `EuclideanGeometry.oangle_pointReflection_right` (Mathlib)
- `Part` (Mathlib)
- `Part.hasFix` (Mathlib)
- `ComplexShape.prev_eq'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_2_C_4.CubeRootLengthReading`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_4.Figure2gOpticalSystem`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_4.HasPreviousPartC3Coordinates`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_4.LengthReading`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_4.NeighboringReflectedRaysGenerateCaustic`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_4.ReflectedLineReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
