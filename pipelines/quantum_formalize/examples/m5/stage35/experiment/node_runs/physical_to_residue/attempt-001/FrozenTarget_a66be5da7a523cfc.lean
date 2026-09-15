import M5ResidueNecessity

theorem M5.ResidueNecessity.anchored_enumeration : ∀ (A : Finset ℕ) (w : ℕ), 0 < w → A.card = w → 0 ∈ A → ∃ u : Fin w → ℕ, Function.Injective u ∧ Finset.univ.image u = A ∧ ∀ i : Fin w, i.val = 0 → u i = 0 := by
  change ∀ (A : Finset ℕ) (w : ℕ), 0 < w → A.card = w → 0 ∈ A → ∃ u : Fin w → ℕ, Function.Injective u ∧ Finset.univ.image u = A ∧ ∀ i : Fin w, i.val = 0 → u i = 0
  intro A w hw hcard hzero
  refine ⟨A.orderEmbOfFin hcard, (A.orderEmbOfFin hcard).injective, Finset.image_orderEmbOfFin_univ A hcard, ?_⟩
  intro i hi
  have hi' : i = ⟨0, hw⟩ := Fin.ext hi
  rw [hi', Finset.orderEmbOfFin_zero hcard hw]
  exact le_antisymm (Finset.min'_le A 0 hzero) (Nat.zero_le _)

theorem M5.ResidueNecessity.reduced_connectivity : ∀ (w N T : ℕ) (hT : 0 < T) (u v : Fin w → ℕ), T ∣ N → M5.Connectivity.supportGcd N (Finset.univ.image u) (Finset.univ.image v) = 1 → M5.BoundedConstruction.tupleSupportGcd (M5.ResidueNecessity.reduceTuple T hT u) (M5.ResidueNecessity.reduceTuple T hT v) = 1 := by
  intro w N T hT u v hTN hconn
  classical
  change Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin w => u i % T)) (Finset.univ.gcd (fun i : Fin w => v i % T))) = 1
  let d := Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin w => u i % T)) (Finset.univ.gcd (fun i : Fin w => v i % T)))
  change d = 1
  have hd : d ∣ T ∧ (∀ i : Fin w, d ∣ u i % T) ∧ (∀ i : Fin w, d ∣ v i % T) := by
    have hh : d ∣ Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin w => u i % T)) (Finset.univ.gcd (fun i : Fin w => v i % T))) := dvd_refl d
    simpa only [Nat.dvd_gcd_iff, Finset.dvd_gcd_iff, Finset.mem_univ, forall_const] using hh
  have lift_dvd : ∀ a : ℕ, d ∣ a % T → d ∣ a := by
    intro a ha
    have hh : d ∣ a % T + T * (a / T) := dvd_add ha (dvd_mul_of_dvd_left hd.1 (a / T))
    simpa only [Nat.mod_add_div] using hh
  apply Nat.eq_one_of_dvd_one
  rw [← hconn]
  apply (M5.Connectivity.support_gcd_dvd N d (Finset.univ.image u) (Finset.univ.image v)).2
  refine ⟨dvd_trans hd.1 hTN, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact lift_dvd (u i) (hd.2.1 i)
  · intro b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact lift_dvd (v i) (hd.2.2 i)

theorem M5.ResidueNecessity.reduced_polynomial : ∀ (w T : ℕ) (hT : 0 < T) (u : Fin w → ℕ), Function.Injective u → AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (Finset.univ.image u)) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofResidueTuple (M5.ResidueNecessity.reduceTuple T hT u)) := by
  classical
  intro w T hT u hu
  change AdjoinRoot.mk (M5.cyclicModulus T)
      (∑ a ∈ Finset.univ.image u, (Polynomial.X : M5.BinaryPolynomial) ^ a) =
    AdjoinRoot.mk (M5.cyclicModulus T)
      (∑ i : Fin w, (Polynomial.X : M5.BinaryPolynomial) ^ (u i % T))
  rw [Finset.sum_image (fun i _ j _ hij => hu hij)]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : u i % T + (u i / T) * T = u i := by
    rw [Nat.mul_comm (u i / T) T]
    exact Nat.mod_add_div (u i) T
  have hp := M5.SupportPolynomial.quotient_monomial_period T (u i % T) (u i / T)
  rw [he] at hp
  exact hp

theorem M5.ResidueNecessity.signature_restriction : ∀ (a b F : M5.BinaryPolynomial) (N T : ℕ), T ∣ N → F ∣ M5.cyclicModulus T → M5.completeSignature a b N = F → M5.completeSignature a b T = F := by
  change ∀ (a b F : M5.BinaryPolynomial) (N T : ℕ), T ∣ N → F ∣ M5.cyclicModulus T → M5.completeSignature a b N = F → M5.completeSignature a b T = F
  intro a b F N T hTN hFT hN
  have hgcd (d x y : M5.BinaryPolynomial) :
      d ∣ EuclideanDomain.gcd x y ↔ d ∣ x ∧ d ∣ y := by
    constructor
    · intro h
      exact ⟨dvd_trans h (EuclideanDomain.gcd_dvd_left x y),
        dvd_trans h (EuclideanDomain.gcd_dvd_right x y)⟩
    · rintro ⟨hx, hy⟩
      exact EuclideanDomain.dvd_gcd hx hy
  have hs (d : M5.BinaryPolynomial) (K : ℕ) :
      d ∣ M5.completeSignature a b K ↔
        d ∣ a ∧ d ∣ b ∧ d ∣ M5.cyclicModulus K := by
    simp only [M5.completeSignature, hgcd]
    tauto
  have hsmall := (hs (M5.completeSignature a b T) T).mp (dvd_refl _)
  have hlarge : F ∣ M5.completeSignature a b N := by
    rw [hN]
  have hFab := (hs F N).mp hlarge
  apply M5.Signature.binary_dvd_antisymm
  · rw [← hN]
    exact (hs _ N).mpr ⟨hsmall.1, hsmall.2.1,
      dvd_trans hsmall.2.2 (M5.Lift.modulus_multiple T N hTN)⟩
  · exact (hs F T).mpr ⟨hFab.1, hFab.2.1, hFT⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w T : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), 0 < w → 0 < T → T ∣ N → F ∣ M5.cyclicModulus T → M5.PhysicalOrder.realizes N w F A B → ∃ r s : Fin w → Fin T, M5.BoundedConstruction.anchoredTuple r ∧ M5.BoundedConstruction.anchoredTuple s ∧ M5.BoundedConstruction.tupleSupportGcd r s = 1 ∧ M5.completeSignature (M5.SupportPolynomial.ofResidueTuple r) (M5.SupportPolynomial.ofResidueTuple s) T = F
