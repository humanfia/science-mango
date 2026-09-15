import FrozenTarget_53f61b51d8e4fb1f
theorem M7.GeneratedLabels.witness : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE i g d k v hsolve
  have hgood := (M7.GeneratedFamily.family_good N w E hw hwN hE i).1
  have hanchor := M7.GeneratedFamily.family_anchored N w E hw hwN hE i
  simp only [M7.PrefixOrbit.ClassValid] at hgood
  have hconn : M7.Connectivity.connected (M7.GeneratedFamily.family N w E i) := by
    aesop
  have hgcd := (M7.Connectivity.anchored_gcd N
    (M7.GeneratedFamily.family N w E i).1
    (M7.GeneratedFamily.family N w E i).2
    hanchor.1 hanchor.2).mp hconn
  apply M7.Transport.actual_witness N w g (M7.GeneratedFamily.family N w E i) d k v
  · aesop
  · aesop
  · exact hanchor.1
  · exact hanchor.2
  · exact hgcd
  · exact hsolve
