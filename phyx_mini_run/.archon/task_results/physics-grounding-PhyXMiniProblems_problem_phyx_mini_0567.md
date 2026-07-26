# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0567.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0567.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:76e7562a4385283a41e38e4a832d2eebac505ba81fbf604e011cf3de8ac2f3cf
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

### Query: `Wavelength Quantity`
- `QuantumMechanics.OneDimension.HarmonicOscillator.one_over_ξ_sq` | module `Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic` | package PhysLean | **Inverse Square of the Characteristic Length.** For a quantum harmonic oscillator with mass $m$, angular frequency $\omega$, and characteristic length $\xi$, the square of the reciprocal of the characteristic length...
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `Signed Wavelength Change Quantity`
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `WickContraction.signInsertSome` | module `Physlib.QFT.PerturbationTheory.WickContraction.Sign.InsertSome` | package PhysLean | Given a Wick contraction `φsΛ` associated with a list of states `φs` and an `i : Fin φs.length.succ`, the change in sign of the contraction associated with inserting `φ` into `φs` at position `i` and contracting it wi...
- `signedDist_zero` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | **Signed Distance with Zero Reference Vector.** The signed distance between any two points $p$ and $q$ relative to the zero vector is $0$.

### Query: `Speed Quantity`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.

### Query: `wavelength Readout`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `Turing.TM1to1.supportsStmt_read` | module `Mathlib.Computability.TuringMachine.PostTuringMachine` | package Mathlib | **Support of the Read Statement.** A finite set of labels $S$ supports a `read` statement if, for every possible symbol $a$ that can be read from the tape, the set $S$ supports the statement $f(a)$ that is executed af...

### Query: `signed Wavelength Change Readout`
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `signedDist_zero` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | **Signed Distance with Zero Reference Vector.** The signed distance between any two points $p$ and $q$ relative to the zero vector is $0$.
- `signedDist_vadd_vadd` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | **Invariance of Signed Distance under Translation.** The signed distance between two points $p$ and $q$ with respect to a reference vector $v$ is invariant under translation by a vector $w$. That is, the signed distan...

### Query: `speed Readout`
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.

### Query: `vacuum Light Speed Readout`
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `SpeedOfLight` | module `Physlib.Relativity.SpeedOfLight` | package PhysLean | The speed of light in a vacuum. An element of this type should be thought of as the speed of light in some chosen but arbitrary system of units.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `Astronomical Source Kind`
- `LengthUnit.astronomicalUnits` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of an astronomical unit (149,597,870,700 meters).
- `stereographic_source` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Domain of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the domain (source) of the stereographic projection associated with $v$ is the complement of the singleton set containing...
- `stereographic'_source` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Domain of the Stereographic Projection.** For an $(n+1)$-dimensional real inner product space $E$ and a point $v$ on the unit sphere in $E$, the domain (source) of the stereographic projection from the sphere with p...

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `QuantumMechanics.OneDimension.HarmonicOscillator.one_over_ξ_sq` (PhysLean)
- `LengthUnit` (PhysLean)
- `Dimension` (PhysLean)
- `signedDist` (Mathlib)
- `WickContraction.signInsertSome` (PhysLean)
- `signedDist_zero` (Mathlib)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitExamples.SpeedEq` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `Turing.TM1to1.supportsStmt_read` (Mathlib)
- `signedDist` (Mathlib)
- `signedDist_zero` (Mathlib)
- `signedDist_vadd_vadd` (Mathlib)
- `UnitExamples.SpeedEq` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimSpeed` (PhysLean)
- `LightProfinite` (Mathlib)
- `SpeedOfLight` (PhysLean)
- `DimSpeed.speedOfLight` (PhysLean)
- `LengthUnit.astronomicalUnits` (PhysLean)
- `stereographic_source` (Mathlib)
- `stereographic'_source` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0567.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.AstronomicalSourceKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.AuxiliaryAxisLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.AuxiliaryFigureObject`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.AuxiliaryFigurePanel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.AuxiliaryObjectGlyph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.AuxiliaryOriginLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.AuxiliaryReferenceFrame`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.DopplerFrame`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.HasPhysicalStellarDopplerParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.IsClosestDisplayedSpeedChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.LightSignalKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.MatchesStellarBlueshiftScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.MatchesSuppliedAuxiliaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.MatchesTwoPercentWavelengthBlueshift`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.MuonEarthReferenceFrameFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.ObserverLocation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.RadialMotion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.SatisfiesApproachingSourceRelativisticDopplerLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.SignedWavelengthChangeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.SpeedQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.StellarBlueshiftSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.VerticalCoordinateRelation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.VerticalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0567.WavelengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
