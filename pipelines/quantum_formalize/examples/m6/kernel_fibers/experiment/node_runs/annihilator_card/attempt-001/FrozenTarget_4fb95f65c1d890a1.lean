import M6KernelFibers

theorem M6.KernelFibers.embed_mk : ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic) (h : M6.KernelFibers.BP), M6.KernelFibers.embed F K hF (AdjoinRoot.mk F h) = AdjoinRoot.mk (F*K) (K*h) := by
  intro F K hF h
  change AdjoinRoot.mk (F * K)
      (K * AdjoinRoot.modByMonicHom hF (AdjoinRoot.mk F h)) =
    AdjoinRoot.mk (F * K) (K * h)
  have hr := AdjoinRoot.mk_leftInverse hF (AdjoinRoot.mk F h)
  change AdjoinRoot.mk F
      (AdjoinRoot.modByMonicHom hF (AdjoinRoot.mk F h)) =
    AdjoinRoot.mk F h at hr
  rw [AdjoinRoot.mk_eq_mk] at hr ⊢
  rcases hr with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    K * AdjoinRoot.modByMonicHom hF (AdjoinRoot.mk F h) - K * h =
        K * (AdjoinRoot.modByMonicHom hF (AdjoinRoot.mk F h) - h) := by ring
    _ = K * (F * q) := by rw [hq]
    _ = (F * K) * q := by ring

theorem M6.KernelFibers.quotient_card : ∀ (F : M6.KernelFibers.BP), F.Monic → Nat.card (AdjoinRoot F) = 2^F.natDegree := by
  change ∀ (F : M6.KernelFibers.BP), F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree
  intro F hF
  let e : AdjoinRoot F ≃ₗ[ZMod 2] (Fin F.natDegree → ZMod 2) :=
    (AdjoinRoot.powerBasisAux' hF).equivFun
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card]

theorem M6.KernelFibers.embed_annihilated : ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic) (z : AdjoinRoot F), AdjoinRoot.mk (F*K) F * M6.KernelFibers.embed F K hF z = 0 := by
  intro F K hF z
  change AdjoinRoot.mk (F * K) F *
      AdjoinRoot.mk (F * K) (K * AdjoinRoot.modByMonicHom hF z) = 0
  rw [← map_mul, AdjoinRoot.mk_eq_zero]
  refine ⟨AdjoinRoot.modByMonicHom hF z, ?_⟩
  ring

theorem M6.KernelFibers.embed_injective : ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic), K ≠ 0 → Function.Injective (M6.KernelFibers.embed F K hF) := by
  change ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic), K ≠ 0 → Function.Injective (M6.KernelFibers.embed F K hF)
  intro F K hF hK x y
  refine AdjoinRoot.induction_on F x ?_
  intro a
  refine AdjoinRoot.induction_on F y ?_
  intro b hab
  rw [M6.KernelFibers.embed_mk, M6.KernelFibers.embed_mk, AdjoinRoot.mk_eq_mk] at hab
  rw [AdjoinRoot.mk_eq_mk]
  rcases hab with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  apply mul_left_cancel₀ hK
  calc
    K * (a - b) = K * a - K * b := by ring
    _ = (F * K) * q := hq
    _ = K * (F * q) := by ring

theorem M6.KernelFibers.embed_surjective_kernel : ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic) (z : AdjoinRoot (F*K)), AdjoinRoot.mk (F*K) F * z = 0 → ∃ t : AdjoinRoot F, M6.KernelFibers.embed F K hF t = z := by
  change ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic) (z : AdjoinRoot (F * K)), AdjoinRoot.mk (F * K) F * z = 0 → ∃ t : AdjoinRoot F, M6.KernelFibers.embed F K hF t = z
  intro F K hF z hz
  obtain ⟨h, rfl⟩ : ∃ h : M6.KernelFibers.BP, AdjoinRoot.mk (F * K) h = z := by
    first
    | exact AdjoinRoot.mk_surjective _ _
    | exact AdjoinRoot.mk_surjective _
  rw [← map_mul, AdjoinRoot.mk_eq_zero] at hz
  rcases hz with ⟨q, hq⟩
  have hh : h = K * q := by
    apply mul_left_cancel₀ hF.ne_zero
    simpa only [mul_assoc] using hq
  refine ⟨AdjoinRoot.mk F q, ?_⟩
  rw [M6.KernelFibers.embed_mk, hh]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (F K : M6.KernelFibers.BP), F.Monic → K ≠ 0 → Nat.card (M6.KernelFibers.annihilator F K) = 2^F.natDegree
