# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0143.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0143.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:e4e3f42fb40841e369766ed6d2bb2cade808ae84e49f306c8e34011e5d292481
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

### Query: `Refraction Interface`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `SetRel.isRefl_iInter` | module `Mathlib.Data.Rel` | package Mathlib | **Reflexivity of the Intersection of Relations.** If $\{R_i\}_{i \in I}$ is a family of reflexive relations on a set, then their intersection $\bigcap_{i \in I} R_i$ is also reflexive.
- `SetRel.isRefl_inter` | module `Mathlib.Data.Rel` | package Mathlib | **Reflexivity of the Intersection of Relations.** If two relations $R_1$ and $R_2$ are both reflexive, then their intersection $R_1 \cap R_2$ is also reflexive.

### Query: `Normal Label`
- `Subgroup.Normal` | module `Mathlib.Algebra.Group.Subgroup.Defs` | package Mathlib | A subgroup `H` is normal if whenever `n ∈ H`, then `g * n * g⁻¹ ∈ H` for every `g : G` [Wikidata Q743179](https://www.wikidata.org/wiki/Q743179)
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `OptionT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Option Transformer Label Mapping.** Given a continuation label that maps optional values of type $\alpha$ to computations in a monad $m$ returning $\beta$, we can construct a corresponding label for the option trans...

### Query: `Ray Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `sameRay_of_mem_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Same Ray Property for Points on a Segment.** If a point $x$ lies on the closed line segment connecting two points $y$ and $z$ in a module over a strictly ordered commutative ring, then the vectors $x - y$ and $z - x...
- `mem_segment_iff_sameRay` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Characterization of Segments via Same Ray.** A point $x$ belongs to the closed segment $[y, z]$ if and only if the vectors $x - y$ and $z - x$ lie on the same ray.

### Query: `incident Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `SimpleGraph.edge_other_incident_set` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | **Incidence of an Edge at its Opposite Vertex.** If an edge $e$ is incident to a vertex $v$ in a simple graph $G$, then $e$ is also incident to the other vertex of $e$ relative to $v$.
- `CategoryTheory.ShortComplex.SnakeInput.L₂'_X₂` | module `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma` | package Mathlib | **Middle Object of the Short Complex $L_2'$.** The middle object of the short complex $L_2'$ is defined as the first object of the short complex $L_3$ in the given snake input.

### Query: `transmitted Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.Factorisation.terminal_mid` | module `Mathlib.CategoryTheory.Category.Factorisation` | package Mathlib | **Terminal Factorization Midpoint.** For a given morphism $f: X \to Y$, the intermediate object (or midpoint) of its terminal factorization is the codomain $Y$.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.

### Query: `incident Ray`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.
- `SimpleGraph.otherVertexOfIncident` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | Given an edge incident to a particular vertex, get the other vertex on the edge.

### Query: `transmitted Ray`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.
- `SameRay.trans` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | `SameRay` is transitive unless the vector in the middle is zero and both other vectors are nonzero.

### Query: `normal`
- `Subgroup.Normal` | module `Mathlib.Algebra.Group.Subgroup.Defs` | package Mathlib | A subgroup `H` is normal if whenever `n ∈ H`, then `g * n * g⁻¹ ∈ H` for every `g : G` [Wikidata Q743179](https://www.wikidata.org/wiki/Q743179)
- `Normal` | module `Mathlib.FieldTheory.Normal.Defs` | package Mathlib | Typeclass for normal field extensions: an algebraic extension of fields `K/F` is *normal* if the minimal polynomial of every element `x` in `K` splits in `K`, i.e. every `F`-conjugate of `x` is in `K`.
- `Norm` | module `Mathlib.Analysis.Normed.Group.Defs` | package Mathlib | Auxiliary class, endowing a type `E` with a function `norm : E → ℝ` with notation `‖x‖`. This class is designed to be extended in more interesting classes specifying the properties of the norm.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `SetRel.isRefl_iInter` (Mathlib)
- `SetRel.isRefl_inter` (Mathlib)
- `Subgroup.Normal` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `OptionT.mkLabel` (Mathlib)
- `segment` (Mathlib)
- `sameRay_of_mem_segment` (Mathlib)
- `mem_segment_iff_sameRay` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `SimpleGraph.edge_other_incident_set` (Mathlib)
- `CategoryTheory.ShortComplex.SnakeInput.L₂'_X₂` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.Factorisation.terminal_mid` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `SameRay` (Mathlib)
- `Module.Ray` (Mathlib)
- `SimpleGraph.otherVertexOfIncident` (Mathlib)
- `SameRay` (Mathlib)
- `Module.Ray` (Mathlib)
- `SameRay.trans` (Mathlib)
- `Subgroup.Normal` (Mathlib)
- `Normal` (Mathlib)
- `Norm` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0143.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0143.AquariumRefractionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0143.HasParallelGlassFaceGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0143.HasPhysicalRefractionConfiguration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0143.IsPhysicalRefractionAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0143.IsUniqueClosestAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0143.MatchesAnswerToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0143.MatchesProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0143.NormalLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0143.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0143.RaySegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0143.RefractionInterface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0143.SatisfiesSnellLawAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
