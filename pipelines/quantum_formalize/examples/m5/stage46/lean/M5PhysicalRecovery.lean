import M5PhysicalRecoveryDependencies

namespace M5.PhysicalRecovery

def decisionCount (N : ℕ) : ℕ := 2 * (N-1)

def selected (N offset : ℕ) (p : List Bool) : Finset ℕ :=
  insert 0 (((Finset.range (N-1)).filter
    (fun i => offset+i < p.length ∧ p[offset+i]? = some true)).image (fun i => i+1))

def available (N offset : ℕ) (p : List Bool) : Finset ℕ :=
  ((Finset.range (N-1)).filter (fun i => p.length ≤ offset+i)).image (fun i => i+1)

def selectedA (N : ℕ) (p : List Bool) := selected N 0 p
def selectedB (N : ℕ) (p : List Bool) := selected N (N-1) p
def availableA (N : ℕ) (p : List Bool) := available N 0 p
def availableB (N : ℕ) (p : List Bool) := available N (N-1) p

def StateOK (N : ℕ) (p : List Bool) : Prop :=
  0 ∈ selectedA N p ∧ 0 ∈ selectedB N p ∧
  selectedA N p ⊆ Finset.range N ∧ selectedB N p ⊆ Finset.range N ∧
  availableA N p ⊆ Finset.range N ∧ availableB N p ⊆ Finset.range N ∧
  Disjoint (selectedA N p) (availableA N p) ∧
  Disjoint (selectedB N p) (availableB N p)

def encode (N : ℕ) (A B : Finset ℕ) : List Bool :=
  List.ofFn (fun j : Fin (decisionCount N) =>
    if j.val < N-1 then decide (j.val+1 ∈ A)
    else decide (j.val-(N-1)+1 ∈ B))

def ValidSupports (N w : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ) : Prop :=
  A ⊆ Finset.range N ∧ B ⊆ Finset.range N ∧ 0 ∈ A ∧ 0 ∈ B ∧
  A.card = w ∧ B.card = w ∧ M5.Connectivity.supportGcd N A B = 1 ∧
  M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) N = F

def wordValid (N w : ℕ) (F : M5.BinaryPolynomial) (q : List Bool) : Prop :=
  q.length = decisionCount N ∧ ValidSupports N w F (selectedA N q) (selectedB N q)

noncomputable def validWords (N w : ℕ) (F : M5.BinaryPolynomial) : Finset (List Bool) := by
  classical
  exact ((Finset.univ : Finset (Fin (decisionCount N) → Bool)).image List.ofFn).filter
    (wordValid N w F)

noncomputable def completionSet (N w : ℕ) (F : M5.BinaryPolynomial) (p : List Bool) :
    Finset (Finset ℕ × Finset ℕ) :=
  M5.ConditionalCount.validCompletions N w F (selectedA N p) (selectedB N p)
    (availableA N p) (availableB N p)

noncomputable def oracle (N w : ℕ) (F : M5.BinaryPolynomial) (p : List Bool) : ℤ :=
  if p.length ≤ decisionCount N then
    M5.ConditionalCount.completionC N w F (selectedA N p) (selectedB N p)
      (availableA N p) (availableB N p)
  else 0

noncomputable def recoverWord (N w : ℕ) (F : M5.BinaryPolynomial) : List Bool :=
  M5.BinaryRecovery.recover (oracle N w F) [] (decisionCount N)

end M5.PhysicalRecovery
