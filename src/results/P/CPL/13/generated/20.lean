

theorem P1_compl_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P1 (Aᶜ) := by
  exact Topology.P1_of_open (A := Aᶜ) hA.isOpen_compl