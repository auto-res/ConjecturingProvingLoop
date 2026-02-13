

theorem P2_compl_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 (Aᶜ) := by
  simpa using (Topology.P2_of_open (A := Aᶜ) hA.isOpen_compl)