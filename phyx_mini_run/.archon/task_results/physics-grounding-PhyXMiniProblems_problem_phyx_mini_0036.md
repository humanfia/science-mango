# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0036.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0036.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:d9aba522e89a9bce54b7d652b6dc82f806c307cf1a57c5d74f587d291bf3b5a2
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

### Query: `Interface Ray`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.
- `Module.Ray.map_symm` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | **Inverse of a Ray Map.** For any linear equivalence $e$ between two modules, the inverse of the induced equivalence between their rays is equal to the ray map induced by the inverse linear equivalence $e^{-1}$.

### Query: `medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `CategoryTheory.Abelian.Preradical.shortComplexObj_X₂` | module `Mathlib.CategoryTheory.Abelian.Preradical.Colon` | package Mathlib | **The Middle Object of the Short Complex Associated with a Preradical.** For any object $X$ in a category $\mathcal{C}$, the middle object (at index 2) of the short complex associated with a preradical is defined as t...

### Query: `degrees To Radians`
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `MvPolynomial.degrees_C` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of a Constant Multivariate Polynomial.** For any element $a$ in a commutative semiring $R$, the multiset of degrees of the constant multivariate polynomial $C(a)$ is empty.

### Query: `Water Glass Interface Diagram`
- `CategoryTheory.GlueData.diagram` | module `Mathlib.CategoryTheory.GlueData` | package Mathlib | (Implementation) The diagram to take colimit of.
- `YoungDiagram` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | A Young diagram is a finite collection of cells on the `ℕ × ℕ` grid such that whenever a cell is present, so are all the ones above and to the left of it. Like matrices, an `(i, j)` cell is a cell in row `i` and colum...
- `YoungDiagram.transpose` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | The `transpose` of a Young diagram is obtained by swapping i's with j's.

### Query: `theta A`
- `Asymptotics.IsTheta` | module `Mathlib.Analysis.Asymptotics.Defs` | package Mathlib | We say that `f` is `Θ(g)` along a filter `l` (notation: `f =Θ[l] g`) if `f =O[l] g` and `g =O[l] f`.
- `Chebyshev.theta` | module `Mathlib.NumberTheory.Chebyshev` | package Mathlib | The sum of `log p` over primes `p ≤ x`.
- `jacobiTheta` | module `Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable` | package Mathlib | Jacobi's one-variable theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τ)`.

### Query: `theta R`
- `Asymptotics.IsTheta` | module `Mathlib.Analysis.Asymptotics.Defs` | package Mathlib | We say that `f` is `Θ(g)` along a filter `l` (notation: `f =Θ[l] g`) if `f =O[l] g` and `g =O[l] f`.
- `Chebyshev.theta` | module `Mathlib.NumberTheory.Chebyshev` | package Mathlib | The sum of `log p` over primes `p ≤ x`.
- `jacobiTheta` | module `Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable` | package Mathlib | Jacobi's one-variable theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τ)`.

### Query: `theta B`
- `Asymptotics.IsTheta` | module `Mathlib.Analysis.Asymptotics.Defs` | package Mathlib | We say that `f` is `Θ(g)` along a filter `l` (notation: `f =Θ[l] g`) if `f =O[l] g` and `g =O[l] f`.
- `Chebyshev.theta` | module `Mathlib.NumberTheory.Chebyshev` | package Mathlib | The sum of `log p` over primes `p ≤ x`.
- `jacobiTheta_eq_jacobiTheta₂` | module `Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable` | package Mathlib | **Relationship between Jacobi Theta Functions.** For any complex number $\tau$, the Jacobi theta function $\theta(\tau)$ is equal to the two-variable Jacobi theta function $\theta(z, \tau)$ evaluated at $z = 0$.

### Query: `Matches Water Glass Figure`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_char` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of a Character Regular Expression.** The language associated with the regular expression representing a single character $a$ is the singleton set containing the string consisting of only that character, den...
- `RegularExpression.matches'_add` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Sum of Regular Expressions.** The language associated with the sum of two regular expressions $P$ and $Q$ is equal to the sum (union) of the languages associated with $P$ and $Q$ individually.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `SameRay` (Mathlib)
- `Module.Ray` (Mathlib)
- `Module.Ray.map_symm` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `CategoryTheory.Abelian.Preradical.shortComplexObj_X₂` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `MvPolynomial.degrees_C` (Mathlib)
- `CategoryTheory.GlueData.diagram` (Mathlib)
- `YoungDiagram` (Mathlib)
- `YoungDiagram.transpose` (Mathlib)
- `Asymptotics.IsTheta` (Mathlib)
- `Chebyshev.theta` (Mathlib)
- `jacobiTheta` (Mathlib)
- `Asymptotics.IsTheta` (Mathlib)
- `Chebyshev.theta` (Mathlib)
- `jacobiTheta` (Mathlib)
- `Asymptotics.IsTheta` (Mathlib)
- `Chebyshev.theta` (Mathlib)
- `jacobiTheta_eq_jacobiTheta₂` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_char` (Mathlib)
- `RegularExpression.matches'_add` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0036.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0036.HasPhysicalOpticalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0036.InterfaceRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0036.MatchesAnswerToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0036.MatchesWaterGlassFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0036.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0036.SatisfiesLawOfReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0036.SatisfiesSnellLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0036.WaterGlassInterfaceDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
