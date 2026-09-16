import M7ActualOrbit
import M7Factorized
namespace M7.ActualFactorized
open M7.Action
abbrev Outer (N : ℕ) := (ZMod N)ˣ × Bool
def toRecord {N : ℕ} [NeZero N] (r : Outer N × ZMod N × ZMod N) : Record N :=
  ⟨r.1.1, r.1.2, r.2.1, r.2.2⟩
def fromRecord {N : ℕ} [NeZero N] (g : Record N) : Outer N × ZMod N × ZMod N :=
  ((g.unit, g.exchange), g.leftShift, g.rightShift)
noncomputable def leftImage {N : ℕ} [NeZero N] (c : Recipe N) (u : Outer N) (s : ZMod N) : Finset (ZMod N) :=
  (if u.2 then c.2 else c.1).image (affine u.1 s)
noncomputable def rightImage {N : ℕ} [NeZero N] (c : Recipe N) (u : Outer N) (t : ZMod N) : Finset (ZMod N) :=
  (if u.2 then c.1 else c.2).image (affine u.1 t)
noncomputable def outerImage {N : ℕ} [NeZero N] (c : Recipe N) (u : Outer N) : Recipe N :=
  act ⟨u.1,u.2,0,0⟩ c
noncomputable def numerator {N : ℕ} [NeZero N] (c : Recipe N) (sector : Outer N → Prop)
    (L R : Finset (ZMod N) → Prop) : ℕ :=
  M7.Factorized.numerator sector (fun u s => L (leftImage c u s)) (fun u t => R (rightImage c u t))
noncomputable def stabilizerNumerator {N : ℕ} [NeZero N] (c : Recipe N) : ℕ :=
  M7.Factorized.exactTargetNumerator (leftImage c) (rightImage c) c.1 c.2
noncomputable def recordCount {N : ℕ} [NeZero N] (c : Recipe N) (sector : Outer N → Prop)
    (L R : Finset (ZMod N) → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter (fun g : Record N => sector (g.unit,g.exchange) ∧ L (act g c).1 ∧ R (act g c).2)).card
def TranslationInvariant {N : ℕ} [NeZero N] (E : Recipe N → Prop) : Prop :=
  ∀ (c : Recipe N) (s t : ZMod N), E (act (translate s t) c) ↔ E c
end M7.ActualFactorized
