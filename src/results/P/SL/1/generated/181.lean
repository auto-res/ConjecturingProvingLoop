

theorem Topology.P1_compl_iff_P2_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ Topology.P2 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := by
    simpa using (isOpen_compl_iff).2 hA
  -- Apply the existing equivalence for open sets.
  simpa using (Topology.P1_iff_P2_of_isOpen (A := Aᶜ) hOpen)