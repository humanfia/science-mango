import M6RecipeIsometries

noncomputable def M6.RecipeTarget.permutation_weight : Prop :=
  ∀ (N : ℕ) [NeZero N] (e : Equiv.Perm (ZMod N)) (a : M6.RecipeIsometries.Block N), M6.Physical.weight N (fun i => a (e i)) = M6.Physical.weight N a

#check M6.RecipeTarget.permutation_weight

noncomputable def M6.RecipeTarget.shift_laws : Prop :=
  ∀ (N : ℕ) [NeZero N] (r : ZMod N) (a : M6.RecipeIsometries.Block N), M6.RecipeIsometries.shift N 0 a = a ∧ M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r a) = a ∧ (M6.RecipeIsometries.shift N r a = 0 ↔ a = 0)

#check M6.RecipeTarget.shift_laws

noncomputable def M6.RecipeTarget.multiply_laws : Prop :=
  ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a : M6.RecipeIsometries.Block N), M6.RecipeIsometries.multiply N 1 a = a ∧ M6.RecipeIsometries.multiply N (u⁻¹) (M6.RecipeIsometries.multiply N u a) = a ∧ (M6.RecipeIsometries.multiply N u a = 0 ↔ a = 0)

#check M6.RecipeTarget.multiply_laws

noncomputable def M6.RecipeTarget.conv_shift : Prop :=
  ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (a h : M6.RecipeIsometries.Block N), M6.Physical.conv N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s h) = M6.RecipeIsometries.shift N (r+s) (M6.Physical.conv N a h)

#check M6.RecipeTarget.conv_shift

noncomputable def M6.RecipeTarget.conv_multiply : Prop :=
  ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a h : M6.RecipeIsometries.Block N), M6.Physical.conv N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u h) = M6.RecipeIsometries.multiply N u (M6.Physical.conv N a h)

#check M6.RecipeTarget.conv_multiply

noncomputable def M6.RecipeTarget.translated_boundary : Prop :=
  ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (a b h : M6.RecipeIsometries.Block N), M6.Physical.boundary N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) h = M6.RecipeIsometries.translateWord N r s (M6.Physical.boundary N a b h)

#check M6.RecipeTarget.translated_boundary

noncomputable def M6.RecipeTarget.translated_syndrome : Prop :=
  ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (a b : M6.RecipeIsometries.Block N) (z : M6.RecipeIsometries.Word N), M6.Physical.syndrome N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) (M6.RecipeIsometries.translateWord N r s z) = M6.RecipeIsometries.shift N (r+s) (M6.Physical.syndrome N a b z)

#check M6.RecipeTarget.translated_syndrome

noncomputable def M6.RecipeTarget.multiplied_boundary : Prop :=
  ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a b h : M6.RecipeIsometries.Block N), M6.Physical.boundary N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) (M6.RecipeIsometries.multiply N u h) = M6.RecipeIsometries.multiplyWord N u (M6.Physical.boundary N a b h)

#check M6.RecipeTarget.multiplied_boundary

noncomputable def M6.RecipeTarget.multiplied_syndrome : Prop :=
  ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a b : M6.RecipeIsometries.Block N) (z : M6.RecipeIsometries.Word N), M6.Physical.syndrome N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) (M6.RecipeIsometries.multiplyWord N u z) = M6.RecipeIsometries.multiply N u (M6.Physical.syndrome N a b z)

#check M6.RecipeTarget.multiplied_syndrome

noncomputable def M6.RecipeTarget.exchange_laws : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b h : M6.RecipeIsometries.Block N) (z : M6.RecipeIsometries.Word N), M6.Physical.boundary N b a h = M6.RecipeIsometries.exchange N (M6.Physical.boundary N a b h) ∧ M6.Physical.syndrome N b a (M6.RecipeIsometries.exchange N z) = M6.Physical.syndrome N a b z

#check M6.RecipeTarget.exchange_laws

noncomputable def M6.RecipeTarget.translated_weight : Prop :=
  ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.translateWord N r s z) = M6.Physical.wordWeight N z

#check M6.RecipeTarget.translated_weight

noncomputable def M6.RecipeTarget.multiplied_weight : Prop :=
  ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.multiplyWord N u z) = M6.Physical.wordWeight N z

#check M6.RecipeTarget.multiplied_weight

noncomputable def M6.RecipeTarget.exchange_weight : Prop :=
  ∀ (N : ℕ) [NeZero N] (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.exchange N z) = M6.Physical.wordWeight N z

#check M6.RecipeTarget.exchange_weight

noncomputable def M6.RecipeTarget.lift_transport : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b a1 b1 : M6.RecipeIsometries.Block N) (P : M6.RecipeIsometries.Word N → M6.RecipeIsometries.Word N) (H : M6.RecipeIsometries.Block N → M6.RecipeIsometries.Block N), Function.Bijective P → Function.Surjective H → (∀ h, M6.Physical.boundary N a1 b1 (H h) = P (M6.Physical.boundary N a b h)) → (∀ z, M6.Physical.syndrome N a1 b1 (P z) = 0 ↔ M6.Physical.syndrome N a b z = 0) → (∀ z, M6.Physical.wordWeight N (P z) = M6.Physical.wordWeight N z) → Function.Bijective (M6.RecipeIsometries.lift N P) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.lift N P) v ∈ M6.Spaces.boundaryWords N (a1) (b1) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.lift N P) v ∈ M6.Spaces.cycleWords N (a1) (b1) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.lift N P) v) = M6.Pinned.weight v

#check M6.RecipeTarget.lift_transport

noncomputable def M6.RecipeTarget.translation_isometry : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N) (r s : ZMod N), Function.Bijective (M6.RecipeIsometries.translate N r s) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.translate N r s) v ∈ M6.Spaces.boundaryWords N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.translate N r s) v ∈ M6.Spaces.cycleWords N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.translate N r s) v) = M6.Pinned.weight v

#check M6.RecipeTarget.translation_isometry

noncomputable def M6.RecipeTarget.multiplier_isometry : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N) (u : (ZMod N)ˣ), Function.Bijective (M6.RecipeIsometries.multiplier N u) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.multiplier N u) v ∈ M6.Spaces.boundaryWords N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.multiplier N u) v ∈ M6.Spaces.cycleWords N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.multiplier N u) v) = M6.Pinned.weight v

#check M6.RecipeTarget.multiplier_isometry

noncomputable def M6.RecipeTarget.exchange_isometry : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N), Function.Bijective (M6.RecipeIsometries.blockExchange N) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.blockExchange N) v ∈ M6.Spaces.boundaryWords N (b) (a) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.blockExchange N) v ∈ M6.Spaces.cycleWords N (b) (a) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.blockExchange N) v) = M6.Pinned.weight v

#check M6.RecipeTarget.exchange_isometry

