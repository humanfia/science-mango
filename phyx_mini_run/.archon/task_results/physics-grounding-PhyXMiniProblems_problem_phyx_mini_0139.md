# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0139.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0139.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:e78cedc11374d887262f1bf0a083b650a0056e39f4a5b51e36ba1d165daf4921
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Gauss law divergence electric field`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.
- `Space.distDiv_inv_pow_eq_dim` | module `Physlib.SpaceAndTime.Space.Norm.Basic` | package PhysLean | The distributional divergence of the radial field `x ↦ ‖x‖ ^ (-d) • x` (i.e. `x / ‖x‖ ^ d`) equals `d * volume (Metric.ball 0 1)` — the surface area of the unit sphere `S^{d-1}` — times the Dirac delta at the origin....

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Length`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.lightYears` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a light year (9,460,730,472,580,800 meters).
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Spherical Mirror Kind`
- `Cosmology.SpatialGeometry.Spherical` | module `Physlib.Cosmology.FLRW.Basic` | package PhysLean | **Spherical Spatial Geometry.** A spherical spatial geometry is characterized by a curvature parameter $k$ that is strictly less than zero.
- `Metric.sphere` | module `Mathlib.Topology.MetricSpace.Pseudo.Defs` | package Mathlib | `sphere x ε` is the set of all points `y` with `dist y x = ε`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`

### Query: `Mirror Role`
- `Polynomial.mirror_eq_iff` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Mirror Symmetry of Polynomials.** For any two polynomials $p$ and $q$, the mirror of $p$ is equal to $q$ if and only if $p$ is equal to the mirror of $q$.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.

### Query: `Figure Element`
- `commutatorElement` | module `Mathlib.Algebra.Group.Commutator` | package Mathlib | The commutator of two elements `g₁` and `g₂`. This is a scoped instance in the `commutatorElement` namespace to avoid clashing with other brackets.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Top` | module `Mathlib.Order.Notation` | package Mathlib | Typeclass for the `⊤` (`\top`) notation

### Query: `Convex Rearview Mirror Setup`
- `Convex` | module `Mathlib.Analysis.Convex.Basic` | package Mathlib | Convexity of sets.
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.
- `Set.Icc.convexComb_assoc_coeff₂'` | module `Mathlib.Topology.UnitInterval` | package Mathlib | Helper definition for `convexComb_assoc'`, giving one of the coefficients appearing when we reassociate a convex combination in the reverse direction.

### Query: `Matches Problem Statement`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `LibraryNote.continuity_lemma_statement` | module `Mathlib.Topology.Continuous` | package Mathlib | The library contains many lemmas stating that functions/operations are continuous. There are many ways to formulate the continuity of operations. Some are more convenient than others. Note: for the most part this note...
- `RegularExpression.matches'_zero` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Empty Regular Expression.** The language associated with the empty regular expression $0$ is the empty language $\emptyset$.

### Query: `Matches Primary Figure`
- `Ideal.primaryComponent` | module `Mathlib.Algebra.Module.Torsion.PrimaryComponent` | package Mathlib | The `I`-primaryComponent component of a module `M` where `I` is an ideal of `A`.
- `Submodule.IsPrimary` | module `Mathlib.RingTheory.IsPrimary` | package Mathlib | A proper submodule `S : Submodule R M` is primary iff `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`. This generalizes `Ideal.IsPrimary`.
- `Ideal.IsPrimary` | module `Mathlib.RingTheory.Ideal.IsPrimary` | package Mathlib | A proper ideal `I` is primary as a submodule.

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Space.distDiv_inv_pow_eq_dim` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `Cosmology.SpatialGeometry.Spherical` (PhysLean)
- `Metric.sphere` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Polynomial.mirror_eq_iff` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `commutatorElement` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Top` (Mathlib)
- `Convex` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `Set.Icc.convexComb_assoc_coeff₂'` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `LibraryNote.continuity_lemma_statement` (Mathlib)
- `RegularExpression.matches'_zero` (Mathlib)
- `Ideal.primaryComponent` (Mathlib)
- `Submodule.IsPrimary` (Mathlib)
- `Ideal.IsPrimary` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0139.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0139.ConvexRearviewMirrorSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0139.FigureElement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0139.IsNearestHundredthReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0139.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0139.MatchesProblemStatement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0139.MirrorRole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0139.OpticalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0139.SatisfiesConvexMirrorFocalLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0139.SatisfiesGaussianMirrorEquation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0139.SatisfiesTransverseMagnificationLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0139.SphericalMirrorKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0139.UsesCartesianConvexMirrorConvention`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
