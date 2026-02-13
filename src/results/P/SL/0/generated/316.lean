

theorem P3_compl_iff_isOpen_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P3 (Aᶜ) ↔ IsOpen ((Aᶜ) : Set X) := by
  have hClosed : IsClosed ((Aᶜ) : Set X) := hA.isClosed_compl
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := (Aᶜ)) hClosed)