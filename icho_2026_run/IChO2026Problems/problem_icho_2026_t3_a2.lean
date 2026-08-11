import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Theory Problem 3, subquestion 3.2 — internal diameter of the
COF-2 honeycomb

58th International Chemistry Olympiad (Tashkent, 2026), Theory Problem T3
*Into Reticular Chemistry*, subquestion 3.2 (3.0 pt).

## Source contract

COF-2 is a honeycomb-type two-dimensional covalent organic framework formed
from a single building block — the phenylene diboronic-acid linker **A2**
(benzene-1,4-diboronic acid) — by self-condensation with loss of water:
three A2 boronic-acid groups cyclocondense into a **boroxine** (B₃O₃) ring,
so each vertex of the hexagonal pore is a boroxine ring and the
para-phenylene cores of A2 span the pore edges between adjacent vertices
(structure figure on T3 page 1).  COF-2 contains no C–O bonds, consistent
with the statement supplying no C–O bond length.  (The companion framework
in the same figure, **COF-1**, is the other chemistry: the
triphenylene-based vertex building block **B3** plus A2, condensed into
boronate ester rings; the present file models COF-2 only.)  The pores of
COF-2 form a regular hexagonal honeycomb.  The subquestion asks for the
internal diameter `d`, in ångström, of one hexagonal pore of COF-2.

### Data supplied by the statement

* C–C/C=C (arenes) bond length `= 1.39 Å`;
* C–B bond length `= 1.56 Å`;
* B–O bond length `= 1.38 Å`;
* the diameter of the circle inscribed in a regular hexagon of side `a` is
  `d = √3 · a`;
* the width of the linkers is to be neglected, so a hexagon side is the bare
  sum of the bond lengths lying along it.

### Structural fact read off the COF-2 figure

Along one side of the hexagonal pore, from boroxine oxygen to boroxine
oxygen, the covalent path runs

```
O–B, B–C, C–C (arene), C–C (arene), C–B, B–O,
```

i.e. two boroxine B–O bonds, two C–B bonds, and the two arene C–C bonds
spanning the para axis of the phenylene linker.  The side length is
therefore `a = 2·(B–O) + 2·(C–C) + 2·(C–B)`.

### Requested conclusion

The numerical value of the internal diameter; the recorded answer is
`d = 15.0 Å`, with the intermediate side length `a = 8.66 Å`.

## Modeling conventions

Following the project convention (cf. `IChO2026Chem.Kinetics`), lengths are
real numerical readouts in the source's unit — here ångström — rather than
dimension-tagged quantities: every datum and the requested answer are already
expressed in ångström, and no unit conversion enters the source problem.
-/

namespace IChO2026.T3.A2

/-- The three bond types occurring along one edge of the COF-2 hexagonal
pore. -/
inductive EdgeBond where
  /-- A boroxine-ring B–O bond. -/
  | boronOxygen
  /-- A C–B bond joining the phenylene linker to a boroxine boron. -/
  | carbonBoron
  /-- An arene C–C/C=C bond of the phenylene linker. -/
  | areneCarbonCarbon
  deriving DecidableEq, Repr

/-- Bond-length data for the COF-2 pore calculation, as real readouts in
ångström. -/
structure BondLengths where
  /-- The arene C–C/C=C bond length. -/
  areneCC : ℝ
  /-- The C–B bond length. -/
  carbonBoron : ℝ
  /-- The B–O bond length. -/
  boronOxygen : ℝ

/-- The bond lengths printed in the statement of subquestion 3.2:
C–C/C=C (arenes) `= 1.39 Å`, C–B `= 1.56 Å`, and B–O `= 1.38 Å`. -/
def statedBondLengths : BondLengths where
  areneCC := 1.39
  carbonBoron := 1.56
  boronOxygen := 1.38

/-- The length of one bond of the given type under bond-length data `L`. -/
def BondLengths.length (L : BondLengths) : EdgeBond → ℝ
  | .boronOxygen => L.boronOxygen
  | .carbonBoron => L.carbonBoron
  | .areneCarbonCarbon => L.areneCC

/-- One edge of the COF-2 hexagonal pore as the ordered list of its bonds,
read off the COF-2 structure figure: starting at the oxygen of one boroxine
(B₃O₃) ring, the path runs O–B and B–C onto the phenylene linker, crosses
the linker's para axis (two arene C–C bonds), and leaves through C–B and
B–O up to the oxygen of the next boroxine ring. -/
def cof2EdgeBonds : List EdgeBond :=
  [.boronOxygen, .carbonBoron, .areneCarbonCarbon, .areneCarbonCarbon,
    .carbonBoron, .boronOxygen]

/-- The side length `a` of a hexagonal pore under bond-length data `L`: the
sum of the bond lengths along one edge.  The statement instructs that the
width of the linkers be neglected, so the side is exactly this bare sum. -/
def hexagonSideLength (L : BondLengths) : ℝ :=
  (cof2EdgeBonds.map L.length).sum

/-- The diameter of the circle inscribed in a regular hexagon of side `a`.
The relation `d = √3 · a` is supplied by the statement of subquestion 3.2. -/
noncomputable def inscribedCircleDiameter (a : ℝ) : ℝ :=
  Real.sqrt 3 * a

/-- The internal diameter `d` of the COF-2 honeycomb pore under bond-length
data `L`, in ångström. -/
noncomputable def internalDiameter (L : BondLengths) : ℝ :=
  inscribedCircleDiameter (hexagonSideLength L)

/-- The side length of the hexagonal pore decomposes as two B–O bond lengths,
two arene C–C bond lengths, and two C–B bond lengths — the bond census of
`cof2EdgeBonds`. -/
theorem hexagonSideLength_eq (L : BondLengths) :
    hexagonSideLength L =
      2 * L.boronOxygen + 2 * L.areneCC + 2 * L.carbonBoron := by
  simp [hexagonSideLength, cof2EdgeBonds, BondLengths.length]
  ring

/-- With the stated bond lengths, the side of the hexagonal pore is
`a = 8.66 Å`. -/
theorem hexagonSideLength_stated :
    hexagonSideLength statedBondLengths = 8.66 := by
  rw [hexagonSideLength_eq]
  norm_num [statedBondLengths]

/-- **Target of subquestion 3.2.**  The internal diameter of the COF-2
honeycomb is `d = √3 · 8.66 Å`, which at the precision of the stated data is
`d = 15.0 Å`: the diameter lies strictly within `0.05 Å` of `15.0 Å`, so it
rounds to `15.0` at one decimal place. -/
theorem internal_diameter_cof2 :
    internalDiameter statedBondLengths = Real.sqrt 3 * 8.66 ∧
      |internalDiameter statedBondLengths - 15.0| < 0.05 := by
  have hsqrt_lo : (1.732 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrt_hi : Real.sqrt 3 < (1.7321 : ℝ) := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hd : internalDiameter statedBondLengths = Real.sqrt 3 * 8.66 := by
    unfold internalDiameter inscribedCircleDiameter
    rw [hexagonSideLength_stated]
  refine ⟨hd, ?_⟩
  rw [hd, abs_lt]
  exact ⟨by linarith, by linarith⟩

end IChO2026.T3.A2
