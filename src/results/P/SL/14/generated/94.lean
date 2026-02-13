

theorem Topology.P2_iff_P3_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P2 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  simpa using
    (Topology.P2_iff_P3_of_isOpen (X := X) (A := Aᶜ) h_open)