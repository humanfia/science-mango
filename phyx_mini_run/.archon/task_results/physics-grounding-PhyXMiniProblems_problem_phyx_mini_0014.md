# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0014.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0014.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:32dbef9f640f554447b360fc2bb14906e3e7a9df07dcd35014f05bef4cdf0d9d
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

### Query: `value In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `angle Of Degrees`
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `Real.Angle.coe_two_pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **The Angle of $2\pi$.** The real number $2\pi$, when considered as an angle, is equal to the zero angle.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)

### Query: `Parallel Mirror Setup`
- `CategoryTheory.Limits.parallelPair` | module `Mathlib.CategoryTheory.Limits.Shapes.Equalizers` | package Mathlib | `parallelPair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with common domain and codomain.
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.
- `CategoryTheory.IsReflexivePair.mk'` | module `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` | package Mathlib | **Reflexive Pair Construction.** A pair of parallel morphisms $f, g: A \to B$ is a reflexive pair if there exists a morphism $s: B \to A$ such that $s \gg f = \text{id}_B$ and $s \gg g = \text{id}_B$.

### Query: `Reflected Beam Trace`
- `Matrix.trace` | module `Mathlib.LinearAlgebra.Matrix.Trace` | package Mathlib | The trace of a square matrix. For more bundled versions, see: * `Matrix.traceAddMonoidHom` * `Matrix.traceLinearMap`
- `Algebra.trace` | module `Mathlib.RingTheory.Trace.Defs` | package Mathlib | The trace of an element `s` of an `R`-algebra is the trace of `(s * ·)`, as an `R`-linear map.
- `LinearMap.IsReflective.reflective_reflection` | module `Mathlib.LinearAlgebra.RootSystem.OfBilinear` | package Mathlib | **Reflectivity of Reflected Vectors.** Let $B$ be a symmetric bilinear form on a module $M$. If $x$ and $y$ are reflective vectors with respect to $B$, then the reflection of $y$ across the hyperplane orthogonal to $x...

### Query: `Has Figure Readout`
- `HasSum` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finite set...
- `HasAdjoint.adjoint` | module `Physlib.Mathematics.InnerProductSpace.Adjoint` | package PhysLean | **Uniqueness of the Adjoint Operator.** If a map $f: E \to F$ between inner product spaces over a field $\mathbb{k}$ has an adjoint $f'$, then the formally defined adjoint operator $f^*$ is equal to $f'$.
- `Turing.TM1to1.supportsStmt_read` | module `Mathlib.Computability.TuringMachine.PostTuringMachine` | package Mathlib | **Support of the Read Statement.** A finite set of labels $S$ supports a `read` statement if, for every possible symbol $a$ that can be read from the tape, the set $S$ supports the statement $f(a)$ that is executed af...

### Query: `Obeys Specular Reflection`
- `Module.reflection` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | Given an element `x` in a module `M` and a linear form `f` on `M` for which `f x = 2`, we define the endomorphism of `M` for which `y ↦ y - (f y) • x`. It is an involutive endomorphism of `M` fixing the kernel of `f`...
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.
- `ComplexShape.Embedding.instIsRelIffOp` | module `Mathlib.Algebra.Homology.Embedding.Basic` | package Mathlib | **Reflectivity of Opposite Embeddings.** If an embedding of complex shapes is reflective, meaning it preserves the relation between indices in both directions, then its opposite embedding is also reflective.

### Query: `left Mirror Reflection Count eq six`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `Polynomial.mirror_eq_iff` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Mirror Symmetry of Polynomials.** For any two polynomials $p$ and $q$, the mirror of $p$ is equal to $q$ if and only if $p$ is equal to the mirror of $q$.
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `JoinedIn` (Mathlib)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `EuclideanGeometry.angle` (Mathlib)
- `Real.Angle.coe_two_pi` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `CategoryTheory.Limits.parallelPair` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `CategoryTheory.IsReflexivePair.mk'` (Mathlib)
- `Matrix.trace` (Mathlib)
- `Algebra.trace` (Mathlib)
- `LinearMap.IsReflective.reflective_reflection` (Mathlib)
- `HasSum` (Mathlib)
- `HasAdjoint.adjoint` (PhysLean)
- `Turing.TM1to1.supportsStmt_read` (Mathlib)
- `Module.reflection` (Mathlib)
- `RootPairing.reflection` (Mathlib)
- `ComplexShape.Embedding.instIsRelIffOp` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Polynomial.mirror_eq_iff` (Mathlib)
- `RootPairing.reflection` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.Problem0014.HasFigureReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.Problem0014.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.Problem0014.ObeysSpecularReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.Problem0014.ParallelMirrorSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.Problem0014.ReflectedBeamTrace`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
