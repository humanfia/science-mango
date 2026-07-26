# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0151.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0151.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:4330cc869f526509cbd10fc9d89ee50ed9647faf8c26288f182d6e11301a5434
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

### Query: `length Value In`
- `LengthUnit.val_ne_zero` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | **Non-zero Length Unit.** For any length unit, its associated numerical value is non-zero.
- `LengthUnit.instInhabited` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | **Default Length Unit.** The type of length units is inhabited, with a default value defined as the positive real number $1$.
- `Computation.length_pure` | module `Mathlib.Data.Seq.Computation` | package Mathlib | **Length of a Pure Computation.** The length of a pure computation of a value $a$ is equal to $0$.

### Query: `nanometers Value`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `spectralValue` | module `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` | package Mathlib | The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial splits into linear factors, then its...

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Film Interface`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `Mathlib.Tactic.LibraryRewrite.RewriteInterface` | module `Mathlib.Tactic.Widget.LibraryRewrite` | package Mathlib | The structure with all data necessary for rendering a rewrite suggestion

### Query: `incident Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `SimpleGraph.edge_other_incident_set` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | **Incidence of an Edge at its Opposite Vertex.** If an edge $e$ is incident to a vertex $v$ in a simple graph $G$, then $e$ is also incident to the other vertex of $e$ relative to $v$.
- `CategoryTheory.ShortComplex.SnakeInput.L₂'_X₂` | module `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma` | package Mathlib | **Middle Object of the Short Complex $L_2'$.** The middle object of the short complex $L_2'$ is defined as the first object of the short complex $L_3$ in the given snake input.

### Query: `transmitted Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.Factorisation.terminal_mid` | module `Mathlib.CategoryTheory.Category.Factorisation` | package Mathlib | **Terminal Factorization Midpoint.** For a given morphism $f: X \to Y$, the intermediate object (or midpoint) of its terminal factorization is the codomain $Y$.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.

### Query: `Film Location`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Lean.Name.location` | module `Physlib.Meta.Basic` | package PhysLean | Returns the location of a name.
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.

### Query: `Reflected Appearance`
- `ComplexShape.Embedding.instIsRelIffOp` | module `Mathlib.Algebra.Homology.Embedding.Basic` | package Mathlib | **Reflectivity of Opposite Embeddings.** If an embedding of complex shapes is reflective, meaning it preserves the relation between indices in both directions, then its opposite embedding is also reflective.
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.
- `AffineEquiv.pointReflection` | module `Mathlib.LinearAlgebra.AffineSpace.AffineEquiv` | package Mathlib | The affine equivalence given by reflection about the point `x`. This is `Equiv.pointReflection` as an `AffineEquiv`.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.val_ne_zero` (PhysLean)
- `LengthUnit.instInhabited` (PhysLean)
- `Computation.length_pure` (Mathlib)
- `LengthUnit.nanometers` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `spectralValue` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `Mathlib.Tactic.LibraryRewrite.RewriteInterface` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `SimpleGraph.edge_other_incident_set` (Mathlib)
- `CategoryTheory.ShortComplex.SnakeInput.L₂'_X₂` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.Factorisation.terminal_mid` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Lean.Name.location` (PhysLean)
- `HahnSeries.leadingCoeff` (Mathlib)
- `ComplexShape.Embedding.instIsRelIffOp` (Mathlib)
- `RootPairing.reflection` (Mathlib)
- `AffineEquiv.pointReflection` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0151.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.FilmInterface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.FilmLocation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.HasPhysicalOpticalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.HasProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.IlluminationKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.MatchesDisplayedThickness`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.MatchesOilFilmFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.OilFilmSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.ReflectedAppearance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.SatisfiesReflectedThinFilmInterference`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0151.VerticalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
