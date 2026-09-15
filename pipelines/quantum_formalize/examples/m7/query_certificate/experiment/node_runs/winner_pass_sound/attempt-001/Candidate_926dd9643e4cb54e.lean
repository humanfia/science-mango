import FrozenTarget_926dd9643e4cb54e
theorem M7.QueryCertificate.winner_pass_sound : QuantumHarnessFrozenTarget := by
  classical
  intro H N inst q bases W dominator hpass
  rcases (M7.QueryCertificate.winner_pass_spec H N q bases W dominator).mp hpass with ⟨hclaimed, hdominator⟩
  have hexact := (M7.GlobalQuery.winners_exact H N q bases).1
  apply Finset.ext
  intro x
  constructor
  · intro hx
    apply (hexact x).mpr
    simpa only [M7.QueryCertificate.strictBetter] using hclaimed x hx
  · intro hx
    by_contra hmissing
    have hwin := (hexact x).mp hx
    rcases hdominator x hwin.1 hmissing with ⟨y, hlookup, hy, hbetter⟩
    apply hwin.2 y (hclaimed y hy).1
    simpa only [M7.QueryCertificate.strictBetter] using hbetter
