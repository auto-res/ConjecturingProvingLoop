

theorem Topology.P3_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P3 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := by
    simpa using (isOpen_compl_iff).2 hA
  -- Every open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := Aᶜ) hOpen