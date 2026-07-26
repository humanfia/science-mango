# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0147.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0147.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:7a59429fbc51175b32042eab35dc4a125b0ab0b64b9a2ef3ff0b0564fdb83dc4
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

### Query: `Prism Face`
- `Affine.Simplex.faceOpposite` | module `Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic` | package Mathlib | The face of a simplex with all but one point.
- `BoxIntegral.Box.face` | module `Mathlib.Analysis.BoxIntegral.Box.Basic` | package Mathlib | Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corners at `I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`.
- `CategoryTheory.ComposableArrows.precomp_δ₀` | module `Mathlib.CategoryTheory.ComposableArrows.Basic` | package Mathlib | **Face Map of a Precomposed Sequence.** For any object $X$ and any morphism $f : X \to F(0)$ from $X$ to the leftmost object of a sequence of $n$ composable arrows $F$, the $0$-th face map $\delta_0$ of the sequence f...

### Query: `Prism Cross Section`
- `crossProduct` | module `Mathlib.LinearAlgebra.CrossProduct` | package Mathlib | The cross product of two vectors in $R^3$ for $R$ a commutative ring.
- `cross_cross` | module `Mathlib.LinearAlgebra.CrossProduct` | package Mathlib | **Vector Triple Product Identity.** For any three vectors $u, v, w \in R^3$ over a commutative ring $R$, the iterated cross product satisfies the identity $u \times (v \times w) = u \times (v \times w) - v \times (u \...
- `Affine.Simplex.closedInterior_inter_shift_eq_homothety` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Shift` | package Mathlib | A parallel cross-section of a simplex is the image of the base under a homothety.

### Query: `Hypotenuse Contact`
- `EuclideanGeometry.dist_div_cos_oangle_right_of_oangle_eq_pi_div_two` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle` | package Mathlib | A side of a right-angled triangle divided by the cosine of the adjacent angle equals the hypotenuse.
- `UpperHalfPlane.center` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Metric` | package Mathlib | Euclidean center of the circle with center `z` and radius `r` in the hyperbolic metric.
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.

### Query: `Sensor Signal`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `HahnSeries.order` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has a nonzero coefficient, the order of 0 is 0.

### Query: `degrees`
- `Polynomial.natDegree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Polynomial.natDegree_eq_of_degree_eq` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | **Equality of Natural Degrees from Equality of Degrees.** For any two polynomials $p$ and $q$ over a semiring $S$, if their degrees are equal, then their natural degrees are also equal.

### Query: `Prism Detector Diagram`
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `YoungDiagram` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | A Young diagram is a finite collection of cells on the `ℕ × ℕ` grid such that whenever a cell is present, so are all the ones above and to the left of it. Like matrices, an `(i, j)` cell is a cell in row `i` and colum...
- `CategoryTheory.detector` | module `Mathlib.CategoryTheory.Generator.Basic` | package Mathlib | Given a category `C` that has a detector (`HasDetector C`), `detector C` is an arbitrarily chosen detector of `C`.

### Query: `Liquid Detector Prism Setup`
- `CategoryTheory.detector` | module `Mathlib.CategoryTheory.Generator.Basic` | package Mathlib | Given a category `C` that has a detector (`HasDetector C`), `detector C` is an arbitrarily chosen detector of `C`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Mathlib.Linter.linter.docPrime` | module `Mathlib.Tactic.Linter.DocPrime` | package Mathlib | The "docPrime" linter emits a warning on declarations that have no doc-string and whose name ends with a `'`. The file `scripts/nolints_prime_decls.txt` contains a list of temporary exceptions to this linter. This lis...

### Query: `Matches Intended Detector Layout`
- `CategoryTheory.detector` | module `Mathlib.CategoryTheory.Generator.Basic` | package Mathlib | Given a category `C` that has a detector (`HasDetector C`), `detector C` is an arbitrarily chosen detector of `C`.
- `CategoryTheory.isDetector_detector` | module `Mathlib.CategoryTheory.Generator.Basic` | package Mathlib | **The Detector of a Category.** In a category $\mathcal{C}$ that has a detector, the specific object designated as the detector of $\mathcal{C}$ satisfies the property of being a detector; that is, the corepresentable...
- `CategoryTheory.HasDetector` | module `Mathlib.CategoryTheory.Generator.Basic` | package Mathlib | For a category `C` and an object `G : C`, `G` is a detector of `C` if the functor `C(G, -)` reflects isomorphisms. While `IsDetector G : Prop` is the proposition that `G` is a detector of `C`, an `HasDetector C : Prop...

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Affine.Simplex.faceOpposite` (Mathlib)
- `BoxIntegral.Box.face` (Mathlib)
- `CategoryTheory.ComposableArrows.precomp_δ₀` (Mathlib)
- `crossProduct` (Mathlib)
- `cross_cross` (Mathlib)
- `Affine.Simplex.closedInterior_inter_shift_eq_homothety` (Mathlib)
- `EuclideanGeometry.dist_div_cos_oangle_right_of_oangle_eq_pi_div_two` (Mathlib)
- `UpperHalfPlane.center` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `HahnSeries.order` (Mathlib)
- `Polynomial.natDegree` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Polynomial.natDegree_eq_of_degree_eq` (Mathlib)
- `LightDiagram'` (Mathlib)
- `YoungDiagram` (Mathlib)
- `CategoryTheory.detector` (Mathlib)
- `CategoryTheory.detector` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Mathlib.Linter.linter.docPrime` (Mathlib)
- `CategoryTheory.detector` (Mathlib)
- `CategoryTheory.isDetector_detector` (Mathlib)
- `CategoryTheory.HasDetector` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0147.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.HasIntendedRayGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.HypotenuseContact`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.IsAllowablePrismIndex`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.LiquidDetectorPrismSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.MatchesIntendedDetectorLayout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.MatchesRoundedAllowableRange`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.PrismCrossSection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.PrismDetectorDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.PrismFace`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.SatisfiesPrismInterfaceOptics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.SatisfiesSensorResponse`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.SensorSignal`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0147.UsesStandardAirWaterIndices`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
