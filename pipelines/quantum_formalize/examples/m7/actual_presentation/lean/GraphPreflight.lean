import M7ActualPresentation
import M7PresentationAccepted

noncomputable def M7.ActualPresentationTarget.decode_encode : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N), M7.ActualPresentation.decode (M7.ActualPresentation.encode g) = g

#check M7.ActualPresentationTarget.decode_encode

noncomputable def M7.ActualPresentationTarget.encode_decode : Prop :=
  ∀ (N : ℕ) [NeZero N] (a : M7.ActualPresentation.Encoded N), M7.ActualPresentation.encode (M7.ActualPresentation.decode a) = a

#check M7.ActualPresentationTarget.encode_decode

noncomputable def M7.ActualPresentationTarget.four_field_order : Prop :=
  ∀ (N : ℕ) [NeZero N] (g h : M7.Action.Record N), (M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h ↔ (g.unit : ZMod N).val < (h.unit : ZMod N).val ∨ (g.unit : ZMod N).val = (h.unit : ZMod N).val ∧ (g.exchange < h.exchange ∨ g.exchange = h.exchange ∧ (g.leftShift.val < h.leftShift.val ∨ g.leftShift.val = h.leftShift.val ∧ g.rightShift.val ≤ h.rightShift.val)))

#check M7.ActualPresentationTarget.four_field_order

noncomputable def M7.ActualPresentationTarget.realize_decode : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (a : M7.ActualPresentation.Encoded N), M7.Presentation.realize (M7.ActualPresentation.leftImage c) (M7.ActualPresentation.rightImage c) a = M7.Action.act (M7.ActualPresentation.decode a) c

#check M7.ActualPresentationTarget.realize_decode

noncomputable def M7.ActualPresentationTarget.domain_univ : Prop :=
  ∀ (N : ℕ) [NeZero N], M7.Presentation.domain (Finset.univ : Finset (M7.ActualPresentation.Outer N)) (Finset.univ : Finset (Fin N)) (Finset.univ : Finset (Fin N)) = (Finset.univ : Finset (M7.ActualPresentation.Encoded N))

#check M7.ActualPresentationTarget.domain_univ

noncomputable def M7.ActualPresentationTarget.leastAction_spec : Prop :=
  ∀ (N : ℕ) [NeZero N] (c q : M7.Action.Recipe N), (∀ g : M7.Action.Record N, M7.ActualPresentation.leastAction c q = some g ↔ M7.Action.act g c = q ∧ ∀ h : M7.Action.Record N, M7.Action.act h c = q → M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h) ∧ (M7.ActualPresentation.leastAction c q = none ↔ ¬ ∃ g : M7.Action.Record N, M7.Action.act g c = q)

#check M7.ActualPresentationTarget.leastAction_spec

noncomputable def M7.ActualPresentationTarget.winning_fiber : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (m : ℕ) (feasible : M7.Action.Recipe N → Prop) (objective : M7.Action.Recipe N → Fin m → ℤ) (mode : M7.Selection.Mode) (g h : M7.Action.Record N), M7.Action.act g c = M7.Action.act h c → (g ∈ M7.ActualPresentation.selected c feasible objective mode ↔ h ∈ M7.ActualPresentation.selected c feasible objective mode)

#check M7.ActualPresentationTarget.winning_fiber

noncomputable def M7.ActualPresentationTarget.presentation_exact : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (m : ℕ) (feasible : M7.Action.Recipe N → Prop) (objective : M7.Action.Recipe N → Fin m → ℤ) (mode : M7.Selection.Mode) (g : M7.Action.Record N), g ∈ M7.ActualPresentation.selected c feasible objective mode → ∃! h : M7.Action.Record N, M7.ActualPresentation.present c feasible objective mode h ∧ M7.Action.act h c = M7.Action.act g c

#check M7.ActualPresentationTarget.presentation_exact

noncomputable def M7.ActualPresentationTarget.presentation_sound : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (m : ℕ) (feasible : M7.Action.Recipe N → Prop) (objective : M7.Action.Recipe N → Fin m → ℤ) (mode : M7.Selection.Mode) (g : M7.Action.Record N), M7.ActualPresentation.present c feasible objective mode g → g ∈ M7.ActualPresentation.selected c feasible objective mode ∧ ∀ h : M7.Action.Record N, M7.Action.act h c = M7.Action.act g c → M7.ActualPresentation.encode g ≤ M7.ActualPresentation.encode h

#check M7.ActualPresentationTarget.presentation_sound

