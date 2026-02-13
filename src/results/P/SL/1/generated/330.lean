

theorem Topology.P3_of_P1_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P2 A → Topology.P3 A := by
  intro hP1 hP2
  -- From `P2` we obtain both `P1` and `P3`; extract the latter.
  exact ((Topology.P2_iff_P1_and_P3 (A := A)).1 hP2).2