

theorem Topology.P1_iff_P2_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ Topology.P2 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  simpa using
    (Topology.P1_iff_P2_of_isOpen (X := X) (A := Aᶜ) h_open)