

theorem P2_complement_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP2 : Topology.P2 A) : Topology.P2 Aᶜ := by
  exact P2_of_open hA.isOpen_compl