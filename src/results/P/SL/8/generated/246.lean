

theorem closed_P1_compl_iff_P3_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA_closed
  simpa using
    Topology.isOpen_P1_iff_P3 (X := X) (A := Aᶜ) h_open