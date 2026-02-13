

theorem P2_compl_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP2 : Topology.P2 A) : Topology.P2 (Aᶜ) := by
  simpa using (Topology.P2_of_open (X := X) (A := Aᶜ) hA.isOpen_compl)