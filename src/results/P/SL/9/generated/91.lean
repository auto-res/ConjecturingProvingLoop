

theorem Topology.P3_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P3 (A := Aᶜ) := by
  have hA_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  exact Topology.P3_of_isOpen (A := Aᶜ) hA_open