import Mathlib

namespace M6.Euclid

abbrev BP := Polynomial (ZMod 2)

noncomputable def rank (p : BP) : ℕ := if p = 0 then 0 else p.natDegree + 1

/-- Leading-term cancellation; subtraction is XOR over the binary coefficient field. -/
noncomputable def cancel (p q : BP) : BP :=
  p - q * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree))

structure Run where
  value : BP
  cancellations : ℕ
  rounds : ℕ
  passes : ℕ

/-- The counters record executed cancellation, recursion and complete-array passes. -/
noncomputable def remainderAux : ℕ → BP → BP → Run
  | 0, p, _ => ⟨p, 0, 0, 1⟩
  | fuel + 1, p, q =>
    if q = 0 ∨ p = 0 ∨ p.degree < q.degree then ⟨p, 0, 0, 1⟩
    else
      let r := remainderAux fuel (cancel p q) q
      ⟨r.value, r.cancellations + 1, 0, r.passes + 2⟩

/-- The extra pass computes the initial degree bound used as fuel. -/
noncomputable def remainder (p q : BP) : Run :=
  let r := remainderAux (rank p) p q
  ⟨r.value, r.cancellations, 0, r.passes + 1⟩

noncomputable def euclidAux : ℕ → BP → BP → Run
  | 0, p, _ => ⟨p, 0, 0, 1⟩
  | fuel + 1, p, q =>
    if q = 0 then ⟨p, 0, 0, 1⟩
    else
      let r := remainder p q
      let g := euclidAux fuel q r.value
      ⟨g.value, r.cancellations + g.cancellations, g.rounds + 1,
        r.passes + g.passes + 1⟩

/-- The initial second-argument degree scan is included in the pass counter. -/
noncomputable def euclid (p q : BP) : Run :=
  let g := euclidAux (rank q + 1) p q
  ⟨g.value, g.cancellations, g.rounds, g.passes + 1⟩

/-- Truncated dense coefficient array in physical increasing coefficient order. -/
noncomputable def dense (N : ℕ) (p : BP) : List (ZMod 2) :=
  List.ofFn (fun i : Fin (N + 1) => p.coeff i)

/-- The actual independent-coordinate shift/XOR array loop. -/
noncomputable def denseXor (N : ℕ) (p q : BP) (shift : ℕ) : List (ZMod 2) :=
  List.ofFn (fun i : Fin (N + 1) =>
    p.coeff i + if shift ≤ (i : ℕ) then q.coeff ((i : ℕ) - shift) else 0)

/-- Increasing-index scan computes the last nonzero position plus one. -/
noncomputable def scanRank (width : ℕ) (p : BP) : ℕ :=
  (List.range width).foldl (fun highest i => if p.coeff i = 0 then highest else i + 1) 0

/-- One complete array pass. At each cell, six width-bit index operations
(comparison, offset subtraction, three addresses and index advance) and four
bit operations (two reads, XOR, write) are conservatively charged. -/
def scanCost (width : ℕ) : ℕ :=
  (List.range width).foldl (fun cost _ => cost + (6 * width + 4)) 0

noncomputable def bitCost (N : ℕ) (p q : BP) : ℕ :=
  (euclid p q).passes * scanCost (N + 1)

/-- Every intermediate operand fits the fixed coefficient-array width. -/
noncomputable def remainderSafe : ℕ → BP → BP → ℕ → Prop
  | 0, p, q, width => rank p ≤ width ∧ rank q ≤ width
  | fuel + 1, p, q, width =>
    rank p ≤ width ∧ rank q ≤ width ∧
      (if q = 0 ∨ p = 0 ∨ p.degree < q.degree then True
       else remainderSafe fuel (cancel p q) q width)

noncomputable def euclidSafe : ℕ → BP → BP → ℕ → Prop
  | 0, p, q, width => rank p ≤ width ∧ rank q ≤ width
  | fuel + 1, p, q, width =>
    rank p ≤ width ∧ rank q ≤ width ∧
      (if q = 0 then True else
       remainderSafe (rank p) p q width ∧
       euclidSafe fuel q (remainder p q).value width)

/-- The two Euclidean computations used for gcd(a,b,M), sharing the first result. -/
noncomputable def preprocess (a b M : BP) : Run :=
  let g := euclid a b
  let h := euclid g.value M
  ⟨h.value, g.cancellations + h.cancellations, g.rounds + h.rounds,
    g.passes + h.passes⟩

noncomputable def preprocessBitCost (N : ℕ) (a b M : BP) : ℕ :=
  (preprocess a b M).passes * scanCost (N + 1)

end M6.Euclid
