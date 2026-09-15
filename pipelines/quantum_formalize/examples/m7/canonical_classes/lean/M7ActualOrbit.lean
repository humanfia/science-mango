import M7ActionGroup
import M7OrbitFibersAccepted
namespace M7.ActualOrbit
open M7.Action
noncomputable def fullStabilizer {N : ℕ} [NeZero N] (c : Recipe N) : Finset (Record N) := by
  classical
  exact Finset.univ.filter (fun g => act g c = c)
noncomputable def stabilizerCount {N : ℕ} [NeZero N] (c : Recipe N) : ℕ := (fullStabilizer c).card
noncomputable def fiberCount {N : ℕ} [NeZero N] (c y : Recipe N) : ℕ := by
  classical
  exact (Finset.univ.filter (fun g : Record N => act g c = y)).card
noncomputable def actionCount {N : ℕ} [NeZero N] (c : Recipe N) (P : Recipe N → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter (fun g : Record N => P (act g c))).card
noncomputable def orbit {N : ℕ} [NeZero N] (c : Recipe N) : Finset (Recipe N) := by
  classical
  exact Finset.univ.image (fun g : Record N => act g c)
noncomputable def distinctCount {N : ℕ} [NeZero N] (c : Recipe N) (P : Recipe N → Prop) : ℕ := by
  classical
  exact ((orbit c).filter P).card
end M7.ActualOrbit
