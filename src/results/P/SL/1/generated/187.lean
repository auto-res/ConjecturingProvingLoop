

theorem Topology.P1_compl_iff_P3_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  -- The complement of a closed set is an open set.
  have hOpen : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA
  -- For open sets, `P1` and `P3` are equivalent.
  simpa using (Topology.P1_iff_P3_of_isOpen (A := Aᶜ) hOpen)