

theorem Topology.P1_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P1 (A := Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := hA.isOpen_compl
  exact Topology.P1_of_isOpen (A := Aᶜ) hOpen