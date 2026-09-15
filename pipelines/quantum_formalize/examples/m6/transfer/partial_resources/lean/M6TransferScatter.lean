import M6TransferTrace
import M6TransferResources
namespace M6.Transfer
abbrev CoefficientAddress (R N : ℕ) := Memory R × Fin (2*N+1)
abbrev CoefficientArray (R N : ℕ) := CoefficientAddress R N → ℤ

def eventDestination {R N : ℕ} (e : ScatterEvent R N) : Option (CoefficientAddress R N) :=
  if h : e.2.2.1.val + e.2.2.2.val < 2*N+1 then
    some (shift e.1 e.2.1, ⟨e.2.2.1.val + e.2.2.2.val, h⟩)
  else none

def eventTerm {R N : ℕ} (W : Memory R → Bit → Polynomial ℤ)
    (input : CoefficientArray R N) (e : ScatterEvent R N) : ℤ :=
  input (e.1, e.2.2.1) * (W e.1 e.2.1).coeff e.2.2.2.val

noncomputable def scatterUpdate {R N : ℕ} (W : Memory R → Bit → Polynomial ℤ)
    (input output : CoefficientArray R N) (e : ScatterEvent R N) : CoefficientArray R N := by
  classical
  exact match eventDestination e with
    | none => output
    | some addr => Function.update output addr (output addr + eventTerm W input e)

noncomputable def scatterEventList (R N : ℕ) : List (ScatterEvent R N) :=
  (Finset.univ : Finset (ScatterEvent R N)).toList

noncomputable def scatterLayer {R N : ℕ} (W : Memory R → Bit → Polynomial ℤ)
    (input : CoefficientArray R N) : CoefficientArray R N :=
  (scatterEventList R N).foldl (scatterUpdate W input) (fun _ => 0)

def encodeCoefficients {R N : ℕ} (v : Memory R → Polynomial ℤ) : CoefficientArray R N :=
  fun addr => (v addr.1).coeff addr.2.val

noncomputable def scalarLayers {R N : ℕ} (W : ℕ → Memory R → Bit → Polynomial ℤ)
    (start : Memory R) : ℕ → CoefficientArray R N
  | 0 => fun addr => if addr.1 = start ∧ addr.2.val = 0 then 1 else 0
  | k+1 => scatterLayer (W k) (scalarLayers W start k)

noncomputable def scalarTraceCoefficient {R : ℕ} (W : ℕ → Memory R → Bit → Polynomial ℤ)
    (N : ℕ) (d : Fin (2*N+1)) : ℤ :=
  ∑ start : Memory R, scalarLayers W start N (start,d)

noncomputable def scalarTracePolynomial {R : ℕ} (W : ℕ → Memory R → Bit → Polynomial ℤ)
    (N : ℕ) : Polynomial ℤ :=
  ∑ d : Fin (2*N+1), Polynomial.monomial d.val (scalarTraceCoefficient W N d)

end M6.Transfer
