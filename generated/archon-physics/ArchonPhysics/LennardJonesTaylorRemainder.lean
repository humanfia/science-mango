import ArchonPhysics.LennardJonesPotential

/-!
# Fourth-order local remainder for the Lennard--Jones bond

The equilibrium-centered Lennard--Jones bond is not exactly quartic.  This
module proves the precise local statement: after subtracting the quartic
FPUT alpha-beta polynomial fixed by its first four derivatives, the remainder
is little-o of `x^4` at zero displacement.
-/

namespace ArchonPhysics.LennardJonesTaylorRemainder

open LennardJonesPotential
open Asymptotics
open scoped Topology

noncomputable section

/-- The homogeneous numerator left after subtracting the fourth-order Taylor
polynomial and extracting the factor `x^5`. -/
def fourthOrderRemainderNumerator (r₀ x : Real) : Real :=
  -3864 * r₀ ^ 11 -
    34916 * x * r₀ ^ 10 -
    147840 * x ^ 2 * r₀ ^ 9 -
    384120 * x ^ 3 * r₀ ^ 8 -
    676940 * x ^ 4 * r₀ ^ 7 -
    846582 * x ^ 5 * r₀ ^ 6 -
    764664 * x ^ 6 * r₀ ^ 5 -
    497870 * x ^ 7 * r₀ ^ 4 -
    228660 * x ^ 8 * r₀ ^ 3 -
    70470 * x ^ 9 * r₀ ^ 2 -
    13104 * x ^ 10 * r₀ -
    1113 * x ^ 11

/-- The rational factor multiplying the fifth power of the displacement in
the exact fourth-order remainder. -/
def fourthOrderRemainderFactor (depth r₀ x : Real) : Real :=
  depth * fourthOrderRemainderNumerator r₀ x /
    (r₀ ^ 4 * (r₀ + x) ^ 12)

/-- Exact algebraic factorization of the fourth-order remainder away from the
Lennard--Jones singular bond length. -/
theorem bondPotential_sub_localAlphaBetaPotential_factor
    {depth r₀ x : Real} (hr₀ : r₀ ≠ 0) (hbond : r₀ + x ≠ 0) :
    bondPotential depth r₀ x - localAlphaBetaPotential depth r₀ x =
      x ^ 5 * fourthOrderRemainderFactor depth r₀ x := by
  unfold bondPotential shiftedPotential rawPotential
  unfold localAlphaBetaPotential harmonicStiffness alphaCoefficient betaCoefficient
  unfold fourthOrderRemainderFactor fourthOrderRemainderNumerator
  field_simp [hr₀, hbond]
  ring

/-- The rational fifth-order factor is continuous at zero whenever the
equilibrium distance is nonzero. -/
theorem continuousAt_fourthOrderRemainderFactor
    {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    ContinuousAt (fourthOrderRemainderFactor depth r₀) 0 := by
  have hnum : ContinuousAt
      (fun x : Real => depth * fourthOrderRemainderNumerator r₀ x) 0 := by
    unfold fourthOrderRemainderNumerator
    fun_prop
  have hden : ContinuousAt
      (fun x : Real => r₀ ^ 4 * (r₀ + x) ^ 12) 0 := by
    fun_prop
  unfold fourthOrderRemainderFactor
  exact hnum.div hden (by simp [hr₀])

/--
The equilibrium-centered Lennard--Jones bond agrees with its local FPUT
alpha-beta polynomial through fourth order.  The statement is genuinely
asymptotic; it does not identify the exact Lennard--Jones bond with a quartic.
-/
theorem bondPotential_sub_localAlphaBetaPotential_isLittleO
    (depth : Real) {r₀ : Real} (hr₀ : r₀ ≠ 0) :
    (fun x : Real =>
        bondPotential depth r₀ x - localAlphaBetaPotential depth r₀ x) =o[𝓝 0]
      (fun x : Real => x ^ 4) := by
  have hpower :
      (fun x : Real => x ^ 5) =o[𝓝 0] (fun x : Real => x ^ 4) :=
    isLittleO_pow_pow (by norm_num)
  have hfactor :
      fourthOrderRemainderFactor depth r₀ =O[𝓝 0]
        (fun _ : Real => (1 : Real)) :=
    (continuousAt_fourthOrderRemainderFactor hr₀).tendsto.isBigO_one Real
  have hproduct :
      (fun x : Real => x ^ 5 * fourthOrderRemainderFactor depth r₀ x) =o[𝓝 0]
        (fun x : Real => x ^ 4) := by
    simpa only [mul_one] using hpower.mul_isBigO hfactor
  apply hproduct.congr'
  · have hcontinuous : ContinuousAt (fun x : Real => r₀ + x) 0 := by
      fun_prop
    filter_upwards [hcontinuous.eventually_ne (by simpa using hr₀)] with x hx
    exact (bondPotential_sub_localAlphaBetaPotential_factor hr₀ hx).symm
  · exact Filter.EventuallyEq.rfl

end

end ArchonPhysics.LennardJonesTaylorRemainder
