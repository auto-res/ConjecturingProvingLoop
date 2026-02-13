

theorem Topology.P3_compl_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 (A := Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := hA.isOpen_compl
  exact Topology.P3_of_isOpen (A := Aᶜ) hOpen