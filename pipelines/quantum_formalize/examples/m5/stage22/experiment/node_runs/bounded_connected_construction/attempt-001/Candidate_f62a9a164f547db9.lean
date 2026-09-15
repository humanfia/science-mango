import FrozenTarget_f62a9a164f547db9
theorem M5.BoundedConstruction.bounded_connected_construction : QuantumHarnessFrozenTarget := by
  intro w T r s hw hT hr hs hg
  have hw0 : 0 < w := by omega
  obtain ⟨e, he, hepos, hpos, hlt, hfeas⟩ :=
    M5.BoundedConstruction.packed_repair_hypotheses w T r s hw hT hr hs hg
  obtain ⟨k, hk, hnew, hcut, hgcd⟩ :=
    M5.BoundedConstruction.repair_parameter w T r s e hT he hpos hlt hfeas
  obtain ⟨hcard, hzero, hrange, hconn⟩ :=
    M5.BoundedConstruction.repaired_support_properties
      w T r s hw hT hr hs e k he hepos hnew hcut hgcd
  refine ⟨M5.RepairSupport.repaired (M5.Packing.packedSupport r) e (e + k * T),
    hcard, M5.Packing.packed_support_card w T s, hzero,
    M5.Packing.packed_support_anchor w T s hw0 (hs ⟨0, hw0⟩ rfl),
    hrange, ?_, hconn, ?_⟩
  · exact fun b hb => M5.Packing.packed_support_range w T s b hb
  · exact (M5.SignatureCongruence.repaired_complete_signature
      (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e k T he hnew).trans
      (M5.SignatureCongruence.packed_complete_signature w T r s)
