# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0100.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0100.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:010ad7b88366b87b68700c931e3f6650a2eac278efa147a370eae709625f0f6a
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Prism Vertex`
- `VertexOperator` | module `Mathlib.Algebra.Vertex.VertexOperator` | package Mathlib | A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-module `V` to Laurent series with coefficients in `V`. We write this as a specialization of the heterogeneous case.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `PrincipalSeg.cocone_pt` | module `Mathlib.CategoryTheory.Limits.Shapes.Preorder.PrincipalSeg` | package Mathlib | **Vertex of the Cocone for a Principal Segment.** Given a principal segment $f$ from a partially ordered set $\alpha$ to a partially ordered set $\beta$ and a functor $F$ from $\beta$ (viewed as a category) to a categ...

### Query: `Prism Face`
- `Affine.Simplex.faceOpposite` | module `Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic` | package Mathlib | The face of a simplex with all but one point.
- `BoxIntegral.Box.face` | module `Mathlib.Analysis.BoxIntegral.Box.Basic` | package Mathlib | Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corners at `I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`.
- `CategoryTheory.ComposableArrows.precomp_δ₀` | module `Mathlib.CategoryTheory.ComposableArrows.Basic` | package Mathlib | **Face Map of a Precomposed Sequence.** For any object $X$ and any morphism $f : X \to F(0)$ from $X$ to the leftmost object of a sequence of $n$ composable arrows $F$, the $0$-th face map $\delta_0$ of the sequence f...

### Query: `Prism Liquid Setup`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Mathlib.Linter.linter.docPrime` | module `Mathlib.Tactic.Linter.DocPrime` | package Mathlib | The "docPrime" linter emits a warning on declarations that have no doc-string and whose name ends with a `'`. The file `scripts/nolints_prime_decls.txt` contains a list of temporary exceptions to this linter. This lis...
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.

### Query: `Matches Prism Figure`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `RegularExpression.matches'_char` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of a Character Regular Expression.** The language associated with the regular expression representing a single character $a$ is the singleton set containing the string consisting of only that character, den...

### Query: `Matches Prism Index Readout`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `Subgroup.index` | module `Mathlib.GroupTheory.Index` | package Mathlib | The index of a subgroup as a natural number. Returns `0` if the index is infinite. [Wikidata Q1464168](https://www.wikidata.org/wiki/Q1464168)
- `RegularExpression.matches'_add` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Sum of Regular Expressions.** The language associated with the sum of two regular expressions $P$ and $Q$ is equal to the sum (union) of the languages associated with $P$ and $Q$ individually.

### Query: `Satisfies Prism Ray Geometry`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `sameRay_of_mem_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Same Ray Property for Points on a Segment.** If a point $x$ lies on the closed line segment connecting two points $y$ and $z$ in a module over a strictly ordered commutative ring, then the vectors $x - y$ and $z - x...
- `ray_eq_iff` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | The rays given by two nonzero vectors are equal if and only if those vectors satisfy `SameRay`.

### Query: `Has Physical Prism Parameters`
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `HasSum` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finite set...
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `Permits Total Internal Reflection`
- `RootPairing.reflectionPerm_self` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | **Involutivity of Reflection Permutations.** For any index $i$ in a root pairing, the associated reflection permutation is its own inverse; that is, applying the permutation corresponding to $i$ twice to any index $j$...
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.
- `Total` | module `Mathlib.Order.Defs.Unbundled` | package Mathlib | `Std.Total` as a definition, suitable for use in proofs.

### Query: `admissible Liquid Refractive Indices`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ADEInequality.Admissible` | module `Mathlib.NumberTheory.ADEInequality` | package Mathlib | A multiset `pqr` of positive natural numbers is `Admissible` if it is equal to `A' q r`, or `D' r`, or one of `E6`, `E7`, or `E8`.
- `Nat.bitIndices` | module `Mathlib.Data.Nat.BitIndices` | package Mathlib | The function which maps each natural number `∑ i ∈ s, 2 ^ i` to the list of elements of `s` in increasing order.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `VertexOperator` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `PrincipalSeg.cocone_pt` (Mathlib)
- `Affine.Simplex.faceOpposite` (Mathlib)
- `BoxIntegral.Box.face` (Mathlib)
- `CategoryTheory.ComposableArrows.precomp_δ₀` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Mathlib.Linter.linter.docPrime` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `LightDiagram'` (Mathlib)
- `RegularExpression.matches'_char` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `Subgroup.index` (Mathlib)
- `RegularExpression.matches'_add` (Mathlib)
- `SameRay` (Mathlib)
- `sameRay_of_mem_segment` (Mathlib)
- `ray_eq_iff` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `HasSum` (Mathlib)
- `Dimension` (PhysLean)
- `RootPairing.reflectionPerm_self` (Mathlib)
- `RootPairing.reflection` (Mathlib)
- `Total` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `ADEInequality.Admissible` (Mathlib)
- `Nat.bitIndices` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0100.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0100.HasPhysicalPrismParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0100.IsClosestAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0100.MatchesPrismFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0100.MatchesPrismIndexReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0100.PermitsTotalInternalReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0100.PrismFace`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0100.PrismLiquidSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0100.PrismVertex`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0100.SatisfiesPrismRayGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
