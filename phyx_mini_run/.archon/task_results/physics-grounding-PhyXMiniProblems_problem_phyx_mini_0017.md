# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0017.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0017.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:5e938e0fb95be243a0b28c4f7bf8c169c7f896ecaaf3daad30cd1e485ea52ff7
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Prism Surface`
- `Mathlib.Linter.linter.docPrime` | module `Mathlib.Tactic.Linter.DocPrime` | package Mathlib | The "docPrime" linter emits a warning on declarations that have no doc-string and whose name ends with a `'`. The file `scripts/nolints_prime_decls.txt` contains a list of temporary exceptions to this linter. This lis...
- `Nat.Prime` | module `Mathlib.Data.Nat.Prime.Defs` | package Mathlib | `Nat.Prime p` means that `p` is a prime number, that is, a natural number at least 2 whose only divisors are `p` and `1`. The theorem `Nat.prime_def` witnesses this description of a prime number.
- `IsPrimal` | module `Mathlib.Algebra.Divisibility.Basic` | package Mathlib | An element `a` in a semigroup is primal if whenever `a` is a divisor of `b * c`, it can be factored as the product of a divisor of `b` and a divisor of `c`.

### Query: `Ray Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `sameRay_of_mem_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Same Ray Property for Points on a Segment.** If a point $x$ lies on the closed line segment connecting two points $y$ and $z$ in a module over a strictly ordered commutative ring, then the vectors $x - y$ and $z - x...
- `mem_segment_iff_sameRay` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Characterization of Segments via Same Ray.** A point $x$ belongs to the closed segment $[y, z]$ if and only if the vectors $x - y$ and $z - x$ lie on the same ray.

### Query: `Answer Choice`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `abs_choice` | module `Mathlib.Algebra.Order.Group.Unbundled.Abs` | package Mathlib | **Absolute Value Choice.** In a linearly ordered group, the absolute value of an element $x$ is equal to either $x$ or its inverse $x^{-1}$.
- `max_choice` | module `Mathlib.Order.MinMax` | package Mathlib | **Maximum Choice.** For any two elements $a$ and $b$ in a linearly ordered set, their maximum is equal to either $a$ or $b$.

### Query: `radians Of Degrees`
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Real.pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` | package Mathlib | The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2], from which one can derive all its properties. For explicit bounds on π, see `Mathlib/Analysis/Real/Pi/Bounds.lean`. Denoted `π`,...
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.

### Query: `degrees Of Radians`
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Polynomial.natDegree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.
- `MvPolynomial.degrees_add_of_disjoint` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of the Sum of Multivariate Polynomials with Disjoint Degrees.** For any two multivariate polynomials $p$ and $q$, if the multisets of their degrees are disjoint, then the degrees of their sum $p + q$ is equa...

### Query: `Is Physical Normal Angle`
- `InnerProductGeometry.angle_normalize_left` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic` | package Mathlib | The angle between a normalized vector and another vector is equal to the angle between the original vectors.
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...

### Query: `Prism Figure Data`
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `CategoryTheory.Pseudofunctor.DescentData'.ofDescentData_hom` | module `Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime` | package Mathlib | **Conversion of Descent Data to Primed Descent Data.** Given a pseudofunctor $F$ and a family of morphisms $f$, any descent data $D$ relative to $f$ can be viewed as a primed descent data relative to a specified colle...
- `PrimeSpectrum.ConstructibleSetData` | module `Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet` | package Mathlib | The data of a constructible set `s` in the prime spectrum of a ring is finitely many tuples `(f, g₁, ..., gₙ)` such that `s = ⋃ (f, g₁, ..., gₙ), V(g₁, ..., gₙ) \ V(f)`. To obtain `s` from its data, use `PrimeSpectrum...

### Query: `Snell Law`
- `EuclideanGeometry.law_sin` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | **Alias** of `EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist`. --- **Law of sines** (sine rule), angle-at-point form.
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `parallelogram_law` | module `Mathlib.Analysis.InnerProductSpace.Basic` | package Mathlib | Parallelogram law

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `Mathlib.Linter.linter.docPrime` (Mathlib)
- `Nat.Prime` (Mathlib)
- `IsPrimal` (Mathlib)
- `segment` (Mathlib)
- `sameRay_of_mem_segment` (Mathlib)
- `mem_segment_iff_sameRay` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `abs_choice` (Mathlib)
- `max_choice` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Real.pi` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Polynomial.natDegree` (Mathlib)
- `MvPolynomial.degrees_add_of_disjoint` (Mathlib)
- `InnerProductGeometry.angle_normalize_left` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `LightDiagram'` (Mathlib)
- `CategoryTheory.Pseudofunctor.DescentData'.ofDescentData_hom` (Mathlib)
- `PrimeSpectrum.ConstructibleSetData` (Mathlib)
- `EuclideanGeometry.law_sin` (Mathlib)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `parallelogram_law` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.Problem0017.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.Problem0017.IsPhysicalNormalAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.Problem0017.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.Problem0017.PrismFigureData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.Problem0017.PrismSurface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.Problem0017.RaySegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.Problem0017.RoundsToHundredthDegree`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.Problem0017.SnellLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.Problem0017.SpecularReflectionLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
