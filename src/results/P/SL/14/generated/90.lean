

theorem Topology.P2_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P2 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  exact Topology.isOpen_implies_P2 (X := X) (A := Aᶜ) h_open