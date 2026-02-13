

theorem Topology.P1_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P1 (A := Aᶜ) := by
  have hA_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  exact Topology.P1_of_isOpen (A := Aᶜ) hA_open