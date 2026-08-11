import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T3-A2: internal diameter of the COF-2 honeycomb

The numerical quantities in this file are lengths measured in ångströms.  The
problem treats the given bond lengths as scalar input data, so their numerical
values are represented by real numbers while the three chemically different
bond types remain distinct constructors.

The pore boundary read from the COF-2 diagram contains two B--O bonds, two
arene C--C/C=C bonds, and two C--B bonds on each honeycomb side.  The requested
diameter is not stored as input data: it is constrained independently by the
inscribed-circle law supplied in the question.
-/

namespace IChO2026Problems.T3A2

/-- The three chemically distinct bond kinds whose lengths are supplied for
the COF-2 pore calculation.  The first constructor covers both arene C--C and
C=C bonds, which the question assigns the same length. -/
private inductive COF2Bond where
  | areneCarbonCarbon
  | carbonBoron
  | boronOxygen
  deriving DecidableEq, Repr

/-- Scalar geometric readout for one COF-2 honeycomb pore, with every length
expressed in ångströms.  The framework topology and the supplied measurement
data are predicates below, rather than fields containing the requested answer.
-/
private structure COF2Honeycomb where
  bondLength : COF2Bond → ℝ
  linkerWidth : ℝ
  sideLength : ℝ
  internalDiameter : ℝ

/-- The empirical bond-length data stated in T3-A2. -/
private def COF2Honeycomb.matchesSuppliedBondLengths (pore : COF2Honeycomb) : Prop :=
  pore.bondLength .areneCarbonCarbon = 1.39 ∧
    pore.bondLength .carbonBoron = 1.56 ∧
      pore.bondLength .boronOxygen = 1.38

/-- The source explicitly directs that the linkers have zero width in this
calculation. -/
private def COF2Honeycomb.neglectsLinkerWidth (pore : COF2Honeycomb) : Prop :=
  pore.linkerWidth = 0

/-- Structural bridge extracted from the COF-2 diagram.  Each pore side has
two B--O, two arene C--C/C=C, and two C--B lengths; a possible linker-width
term is displayed explicitly so that the preceding approximation is not lost.
-/
private def COF2Honeycomb.hasCOF2PoreSide (pore : COF2Honeycomb) : Prop :=
  pore.sideLength =
    2 * pore.bondLength .boronOxygen +
      2 * pore.bondLength .areneCarbonCarbon +
        2 * pore.bondLength .carbonBoron + pore.linkerWidth

/-- The geometric relation supplied in the question for the circle inscribed
in a regular hexagon of side length `a`: `d = √3 a`. -/
private def COF2Honeycomb.obeysInscribedHexagonDiameterLaw
    (pore : COF2Honeycomb) : Prop :=
  pore.internalDiameter = Real.sqrt 3 * pore.sideLength

/-- A real length agrees with a value displayed to one decimal place when it
lies strictly within one half tenth of that displayed value. -/
private def AgreesToOneDecimalPlace (value reported : ℝ) : Prop :=
  |value - reported| < 1 / 20

/-- From the supplied bond data, diagram topology, and zero-width-linker
approximation, the side length of the COF-2 honeycomb is `8.66 Å`.  This
intermediate result is included because the official marking scheme awards
credit for the correctly assembled side-length calculation. -/
private theorem cof2_honeycomb_side_length
    (pore : COF2Honeycomb)
    (hbonds : pore.matchesSuppliedBondLengths)
    (hlinkers : pore.neglectsLinkerWidth)
    (htopology : pore.hasCOF2PoreSide) :
    pore.sideLength = 433 / 50 := by
  rcases hbonds with ⟨harene, hcarbonBoron, hboronOxygen⟩
  rw [htopology, harene, hcarbonBoron, hboronOxygen, hlinkers]
  norm_num

/-- The exact real-number form of the requested COF-2 pore diameter obtained
from the given hexagon law. -/
private theorem cof2_internal_diameter_formula
    (pore : COF2Honeycomb)
    (hbonds : pore.matchesSuppliedBondLengths)
    (hlinkers : pore.neglectsLinkerWidth)
    (htopology : pore.hasCOF2PoreSide)
    (hhexagon : pore.obeysInscribedHexagonDiameterLaw) :
    pore.internalDiameter = Real.sqrt 3 * (433 / 50) := by
  rw [hhexagon, cof2_honeycomb_side_length pore hbonds hlinkers htopology]

/-- T3-A2's requested result: the COF-2 honeycomb has internal diameter
`√3 · 8.66 Å`, which displays as `15.0 Å` to one decimal place.  The reported
decimal is a target rounding guarantee, not an assumption about the pore. -/
theorem cof2_internal_diameter
    (pore : COF2Honeycomb)
    (hbonds : pore.matchesSuppliedBondLengths)
    (hlinkers : pore.neglectsLinkerWidth)
    (htopology : pore.hasCOF2PoreSide)
    (hhexagon : pore.obeysInscribedHexagonDiameterLaw) :
    pore.internalDiameter = Real.sqrt 3 * (433 / 50) ∧
      AgreesToOneDecimalPlace pore.internalDiameter 15.0 := by
  constructor
  · exact cof2_internal_diameter_formula pore hbonds hlinkers htopology hhexagon
  · rw [cof2_internal_diameter_formula pore hbonds hlinkers htopology hhexagon]
    unfold AgreesToOneDecimalPlace
    rw [abs_lt]
    have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      norm_num
    constructor <;> nlinarith

end IChO2026Problems.T3A2
