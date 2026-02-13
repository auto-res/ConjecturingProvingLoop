

theorem P2_iff_P3_of_compl_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  -- The complement of an open set is closed.
  have hClosed : IsClosed ((Aᶜ) : Set X) := hA.isClosed_compl
  -- Apply the existing equivalence for closed sets.
  simpa using
    (Topology.P2_iff_P3_of_isClosed (X := X) (A := (Aᶜ)) hClosed)