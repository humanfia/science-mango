# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0089.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0089.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:8236f248bd75b6beac5451adf33a132311e605c4752452790327af6a3fc7aa25
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

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `Ray Label`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.

### Query: `Mirror Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.

### Query: `Screen Point`
- `CategoryTheory.GrothendieckTopology.Point` | module `Mathlib.CategoryTheory.Sites.Point.Basic` | package Mathlib | Given `J` a Grothendieck topology on a category `C`, a point of the site `(C, J)` consists of a functor `fiber : C ⥤ Type w` such that the category `fiber.Elements` is initially small (which allows defining the fiber...
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `Variable Index Interferometer`
- `Mathlib.Command.Variable.variable?` | module `Mathlib.Tactic.Variable` | package Mathlib | The `variable?` command has the same syntax as `variable`, but it will auto-insert missing instance arguments wherever they are needed. It does not add variables that can already be deduced from others in the current...
- `Subgroup.index` | module `Mathlib.GroupTheory.Index` | package Mathlib | The index of a subgroup as a natural number. Returns `0` if the index is infinite. [Wikidata Q1464168](https://www.wikidata.org/wiki/Q1464168)
- `WeierstrassCurve.VariableChange` | module `Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange` | package Mathlib | An admissible linear change of variables of Weierstrass curves defined over a ring `R` given by a tuple `(u, r, s, t)` for some `u` in `Rˣ` and some `r, s, t` in `R`. As a matrix, it is $$\begin{pmatrix} u^2 & 0 & r \...

### Query: `Has Depicted Coherent Layout`
- `CategoryTheory.coherentTopology` | module `Mathlib.CategoryTheory.Sites.Coherent.Basic` | package Mathlib | The coherent Grothendieck topology on a precoherent category `C`.
- `Mathlib.Tactic.Coherence.coherence_loop` | module `Mathlib.Tactic.CategoryTheory.Coherence` | package Mathlib | **Alias** of `Mathlib.Tactic.Coherence.coherenceLoop`. --- The main part of `coherence` tactic.
- `Mathlib.Tactic.Coherence.warn.refl_coherence` | module `Mathlib.Tactic.CategoryTheory.Coherence` | package Mathlib | If set to `false`, the warning on the use of the deprecated coherence tactic is disabled.

### Query: `Has Physical Optical Parameters`
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `HasSum` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finite set...
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `Is First Dark Fringe On Displayed Scan`
- `IsMinOn` | module `Mathlib.Order.Filter.Extr` | package Mathlib | `IsMinOn f s a` means that `f a ≤ f x` for all `x ∈ s`. Note that we do not assume `a ∈ s`.
- `IsMaxOn` | module `Mathlib.Order.Filter.Extr` | package Mathlib | `IsMaxOn f s a` means that `f x ≤ f a` for all `x ∈ s`. Note that we do not assume `a ∈ s`.
- `FirstOrder.Language.LHom.IsExpansionOn` | module `Mathlib.ModelTheory.LanguageMap` | package Mathlib | A language homomorphism is an expansion on a structure if it commutes with the interpretation of all symbols on that structure.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `SameRay` (Mathlib)
- `RayVector` (Mathlib)
- `Module.Ray` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `CategoryTheory.GrothendieckTopology.Point` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `Mathlib.Command.Variable.variable?` (Mathlib)
- `Subgroup.index` (Mathlib)
- `WeierstrassCurve.VariableChange` (Mathlib)
- `CategoryTheory.coherentTopology` (Mathlib)
- `Mathlib.Tactic.Coherence.coherence_loop` (Mathlib)
- `Mathlib.Tactic.Coherence.warn.refl_coherence` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `HasSum` (Mathlib)
- `Dimension` (PhysLean)
- `IsMinOn` (Mathlib)
- `IsMaxOn` (Mathlib)
- `FirstOrder.Language.LHom.IsExpansionOn` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0089.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.HasDepictedCoherentLayout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.HasPhysicalOpticalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.IsCorrectAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.IsFirstDarkFringeOnDisplayedScan`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.MatchesStatedAndGraphReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.MirrorLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.RayLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.SatisfiesOpticalPathDifferenceLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.SatisfiesPhaseDifferenceLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.SatisfiesTwoBeamInterferenceLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.ScreenPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0089.VariableIndexInterferometer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
