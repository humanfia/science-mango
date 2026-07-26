# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0973.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0973.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:9e4b69f2bad31da40f1c5c704fc3448cd0e4c3fcafe0b76d72d182f62b131f19
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `electric charge`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `ChargeUnit.elementaryCharge` | module `Physlib.Electromagnetism.Charge.ChargeUnit` | package PhysLean | The charge unit of a elementryCharge (1.602176634×10−19 coulomb).
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `area Dimension`
- `DimArea` | module `Physlib.Units.WithDim.Area` | package PhysLean | The type of areas in the absence of a choice of unit.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `Order.krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | The **Krull dimension** of a preorder `α` is the supremum of the rightmost index of all relation series of `α` ordered by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull dimension is defined to...

### Query: `electric Current Dimension`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Dimension.C𝓭` | module `Physlib.Units.Dimension` | package PhysLean | The dimension corresponding to charge.
- `Electromagnetism.ThreeDimension.electricField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The electric field written in terms of the scalar and vector potentials as `- ∇ φ - ∂ₜ A`.

### Query: `magnetic Flux Density Dimension`
- `Electromagnetism.MagneticField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The magnetic field is a map from `d+1` dimensional spacetime to the vector space `ℝ^d`.
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The magnetic field written as the curl of the vector potential as `∇ ⨯ A`.

### Query: `area Rate Dimension`
- `DimArea` | module `Physlib.Units.WithDim.Area` | package PhysLean | The type of areas in the absence of a choice of unit.
- `ringKrullDim` | module `Mathlib.RingTheory.KrullDimension.Basic` | package Mathlib | The ring-theoretic Krull dimension is the Krull dimension of its spectrum ordered by inclusion.
- `DimArea.hectare` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 hectare (10,000 square meters).

### Query: `magnetic Flux Dimension`
- `Electromagnetism.MagneticField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The magnetic field is a map from `d+1` dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The matrix corresponding to the magnetic field in general dimensions. In `3` space-dimensions this reduces to a vector.
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The magnetic field written as the curl of the vector potential as `∇ ⨯ A`.

### Query: `magnetic Flux Rate Dimension`
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The matrix corresponding to the magnetic field in general dimensions. In `3` space-dimensions this reduces to a vector.
- `Electromagnetism.MagneticField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The magnetic field is a map from `d+1` dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The magnetic field written as the curl of the vector potential as `∇ ⨯ A`.

### Query: `electromotive Force Dimension`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Dimension.C𝓭` | module `Physlib.Units.Dimension` | package PhysLean | The dimension corresponding to charge.
- `Dimension.L𝓭_charge` | module `Physlib.Units.Dimension` | package PhysLean | **Electric Charge of the Length Dimension.** The electric charge component of the length dimension is zero.

### Query: `electrical Resistance Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `Dimension.C𝓭` | module `Physlib.Units.Dimension` | package PhysLean | The dimension corresponding to charge.

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `ChargeUnit.elementaryCharge` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `DimArea` (PhysLean)
- `dimH` (Mathlib)
- `Order.krullDim` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Dimension.C𝓭` (PhysLean)
- `Electromagnetism.ThreeDimension.electricField_eq_3D` (PhysLean)
- `Electromagnetism.MagneticField` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` (PhysLean)
- `DimArea` (PhysLean)
- `ringKrullDim` (Mathlib)
- `DimArea.hectare` (PhysLean)
- `Electromagnetism.MagneticField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` (PhysLean)
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` (PhysLean)
- `Electromagnetism.MagneticField` (PhysLean)
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Dimension.C𝓭` (PhysLean)
- `Dimension.L𝓭_charge` (PhysLean)
- `Dimension` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `Dimension.C𝓭` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0973.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.AnswerMatchesInducedCurrent`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.AreaRateMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.CircuitModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.DescribesUniformMagneticFieldRegion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.ElectricCurrentMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.EmfMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.EnteringRectangularLoopSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.FieldLoopOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.HasPhysicalEnteringLoopParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.LoopDimension`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.MagneticFieldGlyph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.MagneticFluxDensityMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.MagneticFluxRateMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.MatchesSuppliedRectangularLoopFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.MatchesWrittenEnteringScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.MotionRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.PageNormalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.PlanarDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.RectangularCircuit`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.RectangularLoopFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.RegionWidthRelation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.ResistanceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.SatisfiesEnteringFaradayAndOhmLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.SpeedQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.TraversalPhase`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.UniformMagneticFieldRegion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0973.VerticalEdge`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
