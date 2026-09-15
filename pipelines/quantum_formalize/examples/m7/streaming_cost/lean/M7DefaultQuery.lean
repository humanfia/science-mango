import M7Transport
import M7Selection
import M7ActualPresentation
open scoped BigOperators

namespace M7.DefaultQuery
inductive SectorMode where
  | classSector
  | placementSector
  deriving DecidableEq
inductive Coordinate where
  | locality
  | radius
  | negativeDimension
  | negativeDistance
  deriving DecidableEq
inductive QueryError where
  | invalidSignature
  deriving DecidableEq
structure Query where
  dimensions : Finset ℕ
  signatures : Option (Finset M6.Cyclic.BinaryPolynomial)
  sectorMode : SectorMode
  distanceFloor : Option ℤ
  localityCap : Option ℕ
  radiusCap : Option ℕ
  objectives : List Coordinate
  order : M7.Selection.Mode

def delta (N : ℕ) (i : ZMod N) : ℕ := min i.val (N-i.val)
noncomputable def blockLocality {N : ℕ} (A : Finset (ZMod N)) : ℕ := ∑ i ∈ A, delta N i
noncomputable def blockRadius {N : ℕ} (A : Finset (ZMod N)) : ℕ := A.sup (delta N)
noncomputable def locality {N : ℕ} (c : M7.Action.Recipe N) : ℕ := blockLocality c.1 + blockLocality c.2
noncomputable def radius {N : ℕ} (c : M7.Action.Recipe N) : ℕ := max (blockRadius c.1) (blockRadius c.2)
noncomputable def signature {N : ℕ} (c : M7.Action.Recipe N) := M7.Domain.signature c.1 c.2
noncomputable def dimension {N : ℕ} (c : M7.Action.Recipe N) : ℕ := 2*(signature c).natDegree
noncomputable def distance {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Option ℕ := M7.Transport.distance c

def valid (N : ℕ) (q : Query) : Prop :=
  match q.signatures with
  | none => True
  | some E => ∀ F ∈ E, F.Monic ∧ F ∣ M6.Cyclic.modulus N

def allows (q : Query) (F : M6.Cyclic.BinaryPolynomial) : Prop :=
  match q.signatures with
  | none => True
  | some E => F ∈ E
noncomputable def sectorTest {N : ℕ} [NeZero N] (q : Query)
    (base placed : M7.Action.Recipe N) : Prop :=
  match q.sectorMode with
  | .classSector => ∃ g : M7.Action.Record N, allows q (signature (M7.Action.act g base))
  | .placementSector => allows q (signature placed)
def needsDistance (q : Query) : Prop := q.distanceFloor.isSome ∨ .negativeDistance ∈ q.objectives
noncomputable def floorTest {N : ℕ} [NeZero N] (q : Query) (c : M7.Action.Recipe N) : Prop :=
  match q.distanceFloor with
  | none => True
  | some floor => ∃ d, distance c = some d ∧ floor ≤ (d : ℤ)
noncomputable def feasible {N : ℕ} [NeZero N] (q : Query) (base placed : M7.Action.Recipe N) : Prop :=
  valid N q ∧ dimension placed ∈ q.dimensions ∧ sectorTest q base placed ∧
  (needsDistance q → (distance placed).isSome) ∧ floorTest q placed ∧
  (match q.localityCap with | none => True | some cap => locality placed ≤ cap) ∧
  (match q.radiusCap with | none => True | some cap => radius placed ≤ cap)

/-- The zero default is used only to totalize comparisons on rejected NoLogical records;
feasible excludes them whenever negativeDistance is an objective. No infinite distance is assigned. -/
noncomputable def coordinate {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Coordinate → ℤ
  | .locality => (locality c : ℤ)
  | .radius => (radius c : ℤ)
  | .negativeDimension => -(dimension c : ℤ)
  | .negativeDistance => -((distance c).getD 0 : ℤ)
noncomputable def objective {N : ℕ} [NeZero N] (q : Query) (c : M7.Action.Recipe N)
    (i : Fin q.objectives.length) : ℤ := coordinate c (q.objectives.get i)
noncomputable def winners {N : ℕ} [NeZero N] (q : Query) (base : M7.Action.Recipe N) : Finset (M7.Action.Record N) :=
  M7.Selection.select Finset.univ (fun g => feasible q base (M7.Action.act g base))
    (fun g => objective q (M7.Action.act g base)) q.order
noncomputable def answer {N : ℕ} [NeZero N] (q : Query) (base : M7.Action.Recipe N) : Except QueryError (Finset (M7.Action.Record N)) := by
  classical
  exact if valid N q then .ok (winners q base) else .error .invalidSignature

noncomputable def present {N : ℕ} [NeZero N] (q : Query) (base : M7.Action.Recipe N) (g : M7.Action.Record N) : Prop :=
  M7.ActualPresentation.present base (feasible q base) (objective q) q.order g
end M7.DefaultQuery
