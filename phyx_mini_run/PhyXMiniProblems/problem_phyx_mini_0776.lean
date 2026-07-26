import Mathlib
import Physlib.ClassicalMechanics.RigidBody.Basic
import Physlib.Units.WithDim.Basic

open MeasureTheory

namespace PhyXMini0776

open Dimension

/-- The coordinate direction of the cone's axis in the body-fixed frame from the figure. -/
def symmetryAxisIndex : Fin 3 := 2

/-- The line labelled `Axis` in the figure: the third coordinate axis. -/
def symmetryAxisLine : Set (Space 3) :=
  {x | x 0 = 0 ∧ x 1 = 0}

/-- The solid right circular cone shown in the figure, with its apex at the origin,
its base in the plane `x₂ = altitude`, and its radius there equal to `radius`.
Coordinates and the values of `altitude` and `radius` are measured in the same length unit. -/
def solidRightCircularConeRegion
    (altitude radius : WithDim L𝓭 ℝ) : Set (Space 3) :=
  {x |
    0 ≤ x symmetryAxisIndex ∧
    x symmetryAxisIndex ≤ altitude.val ∧
    x 0 ^ 2 + x 1 ^ 2 ≤
      (radius.val / altitude.val * x symmetryAxisIndex) ^ 2}

/-- The physical moment of inertia about the line labelled `Axis` in the figure.
The dimension tag records the dimension `mass * length * length`. -/
noncomputable def momentOfInertiaAboutSymmetryAxis
    (body : RigidBody 3) : WithDim (M𝓭 * L𝓭 * L𝓭) ℝ :=
  ⟨body.inertiaTensor symmetryAxisIndex symmetryAxisIndex⟩

/-- The governing model for a uniform solid cone. The rigid body's mass distribution is
constant on `solidRightCircularConeRegion` and zero outside it. The coefficient is the
uniform density obtained from the cone volume `π R² h / 3`.

This predicate contains the setup and governing law only; it does not assume a formula for
the moment of inertia. -/
def IsUniformSolidRightCircularCone
    (body : RigidBody 3)
    (mass : WithDim M𝓭 ℝ)
    (altitude radius : WithDim L𝓭 ℝ) : Prop :=
  0 < mass ∧
  0 < altitude ∧
  0 < radius ∧
  body.mass = mass.val ∧
  ∀ (f : Space 3 → ℝ) (hf : ContDiff ℝ ⊤ f),
    body.ρ (RigidBody.cmap f hf) =
      (3 * mass.val / (Real.pi * radius.val ^ 2 * altitude.val)) *
        ∫ x in solidRightCircularConeRegion altitude radius, f x ∂volume

/-- For a uniform solid right circular cone, the moment of inertia about its symmetry axis is
`3/10 M R²`. This is answer choice B.

Blueprint: `thm:physics:phyx_mini_0776:target`. -/
theorem uniformSolidCone_momentOfInertia_about_symmetryAxis
    (body : RigidBody 3)
    (mass : WithDim M𝓭 ℝ)
    (altitude radius : WithDim L𝓭 ℝ)
    (hcone : IsUniformSolidRightCircularCone body mass altitude radius) :
    momentOfInertiaAboutSymmetryAxis body =
      ⟨(3 / 10 : ℝ) * mass.val * radius.val ^ 2⟩ := by
  sorry

end PhyXMini0776
