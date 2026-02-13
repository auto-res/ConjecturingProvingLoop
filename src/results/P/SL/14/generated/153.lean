

theorem Topology.P2_iff_P3_compl_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_open : IsOpen A) :
    Topology.P2 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  -- The complement of an open set is closed.
  have h_closed : IsClosed (Aᶜ) := by
    simpa using hA_open.isClosed_compl
  -- Apply the existing equivalence for closed sets.
  simpa using
    (Topology.P2_iff_P3_of_isClosed (X := X) (A := Aᶜ) h_closed)