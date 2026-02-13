

theorem Topology.P3_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ : Set X) := hA_closed.isOpen_compl
  exact Topology.P3_of_open hOpen