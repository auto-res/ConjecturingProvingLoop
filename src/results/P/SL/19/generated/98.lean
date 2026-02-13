

theorem Topology.P2_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 (A := Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := hA.isOpen_compl
  exact Topology.P2_of_isOpen (A := Aᶜ) hOpen