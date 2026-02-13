

theorem Topology.P2_compl_iff_P3_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P2 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := by
    simpa using (isOpen_compl_iff).2 hA
  -- Apply the existing equivalence for open sets.
  simpa using (Topology.P2_iff_P3_of_isOpen (A := Aᶜ) hOpen)