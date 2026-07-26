# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0494.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0494.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Volume Quantity`
- `Real.volume_real_Ico` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Volume of a Left-Closed, Right-Open Real Interval.** For any two real numbers $a$ and $b$, the real-valued volume of the interval $[a, b)$ is equal to the maximum of $b - a$ and $0$.
- `Orientation.volumeForm` | module `Mathlib.Analysis.InnerProductSpace.Orientation` | package Mathlib | The volume form on an oriented real inner product space, a nonvanishing top-dimensional alternating form uniquely defined by compatibility with the orientation and inner product structure.
- `NVEHamiltonian.V` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.Basic` | package PhysLean | Helper to get the volume in an N-V Hamiltonian

### Query: `energy In Joules`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `pressure In Pascals`
- `padicValNat` | module `Mathlib.Data.Nat.MaxPowDiv` | package Mathlib | For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`.
- `DimPressure.pascal` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 pascal, Pa.
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..

### Query: `volume In Cubic Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `Cubic.toPoly` | module `Mathlib.Algebra.CubicDiscriminant` | package Mathlib | Convert a cubic polynomial to a polynomial.
- `Space.volume_metricBall_three_real` | module `Physlib.SpaceAndTime.Space.Integrals.Basic` | package PhysLean | **Volume of the Unit Ball in Three-Dimensional Space.** The volume of the unit metric ball centered at the origin in $\mathbb{R}^3$ is equal to $\frac{4}{3}\pi$.

### Query: `State Label`
- `StateT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **State Monad Transformer Label Mapping.** Given a continuation label that maps a pair consisting of a value and a state to a computation in a base monad, this construction defines a corresponding label for the state...
- `StateT.goto_mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **State Transformer Continuation Jump.** For a continuation label $x$ that maps pairs of values and states to computations in a base monad $m$, jumping to the state-transformed version of $x$ with a value $i$ is equiv...
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.

### Query: `Process Path`
- `MeasureTheory.IsStronglyProgressive` | module `Mathlib.Probability.Process.Adapted` | package Mathlib | Strongly progressive process. A sequence of functions `u` is said to be strongly progressive with respect to a filtration `f` if at each point in time `i`, `u` restricted to `Set.Iic i × Ω` is strongly measurable with...
- `MeasureTheory.stoppedProcess` | module `Mathlib.Probability.Process.Stopping` | package Mathlib | Given a map `u : ι → Ω → E`, the stopped process with respect to `τ` is `u i ω` if `i ≤ τ ω`, and `u (τ ω) ω` otherwise. Intuitively, the stopped process stops evolving once the stopping time has occurred.
- `Path` | module `Mathlib.Topology.Path` | package Mathlib | Continuous path connecting two points `x` and `y` in a topological space

### Query: `path Start`
- `Quiver.Path.start_mem_vertices` | module `Mathlib.Combinatorics.Quiver.Path.Vertices` | package Mathlib | **Start Vertex Membership.** For any path in a quiver from a vertex $a$ to a vertex $b$, the starting vertex $a$ is always contained in the set of vertices of the path.
- `Path` | module `Mathlib.Topology.Path` | package Mathlib | Continuous path connecting two points `x` and `y` in a topological space
- `Quiver.Path.vertices_head?` | module `Mathlib.Combinatorics.Quiver.Path.Vertices` | package Mathlib | The head of the vertices list is the start vertex

### Query: `path Finish`
- `Path` | module `Mathlib.Topology.Path` | package Mathlib | Continuous path connecting two points `x` and `y` in a topological space
- `Quiver.Path.end_cons` | module `Mathlib.Combinatorics.Quiver.Path.Vertices` | package Mathlib | **End Vertex of a Path Extension.** For any path $p$ from vertex $a$ to vertex $b$ and any edge $e$ from $b$ to vertex $c$, the end vertex of the path formed by appending $e$ to $p$ is $c$.
- `Mathlib.Tactic.TFAE.tfaeFinish` | module `Mathlib.Tactic.TFAE` | package Mathlib | `tfae_finish` closes goals of the form `TFAE [P₁, P₂, ...]` once a sufficient collection of hypotheses of the form `Pᵢ → Pⱼ` or `Pᵢ ↔ Pⱼ` have been introduced to the local context. `tfae_have` can be used to convenien...

### Query: `Path Geometry`
- `Path` | module `Mathlib.Topology.Path` | package Mathlib | Continuous path connecting two points `x` and `y` in a topological space
- `SimpleGraph.Walk.IsPath` | module `Mathlib.Combinatorics.SimpleGraph.Paths` | package Mathlib | A *path* is a walk with no repeating vertices. Use `SimpleGraph.Walk.IsPath.mk'` for a simpler constructor.
- `Manifold.pathELength_eq_lintegral_mfderiv_Icc` | module `Mathlib.Geometry.Manifold.Riemannian.PathELength` | package Mathlib | **Path Length as the Integral of the Speed.** The length of a path $\gamma$ between the parameters $a$ and $b$ is equal to the lower Lebesgue integral of the norm of its manifold derivative over the closed interval $[...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Real.volume_real_Ico` (Mathlib)
- `Orientation.volumeForm` (Mathlib)
- `NVEHamiltonian.V` (PhysLean)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `padicValNat` (Mathlib)
- `DimPressure.pascal` (PhysLean)
- `DimPressure` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `Cubic.toPoly` (Mathlib)
- `Space.volume_metricBall_three_real` (PhysLean)
- `StateT.mkLabel` (Mathlib)
- `StateT.goto_mkLabel` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `MeasureTheory.IsStronglyProgressive` (Mathlib)
- `MeasureTheory.stoppedProcess` (Mathlib)
- `Path` (Mathlib)
- `Quiver.Path.start_mem_vertices` (Mathlib)
- `Path` (Mathlib)
- `Quiver.Path.vertices_head?` (Mathlib)
- `Path` (Mathlib)
- `Quiver.Path.end_cons` (Mathlib)
- `Mathlib.Tactic.TFAE.tfaeFinish` (Mathlib)
- `Path` (Mathlib)
- `SimpleGraph.Walk.IsPath` (Mathlib)
- `Manifold.pathELength_eq_lintegral_mfderiv_Icc` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0494.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0494.AxisQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0494.GasPVExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0494.MatchesPrimaryPVDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0494.MatchesProblemStatement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0494.ObeysThermodynamicLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0494.PVDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0494.PathGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0494.ProcessKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0494.ProcessPath`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0494.StateLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0494.ThermodynamicState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0494.VolumeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
