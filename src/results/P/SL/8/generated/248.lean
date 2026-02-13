

theorem closed_P2_compl_iff_P3_compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hA_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA_closed
  -- Use the existing equivalence for open sets.
  simpa using
    Topology.isOpen_P2_iff_P3 (X := X) (A := Aᶜ) hA_open