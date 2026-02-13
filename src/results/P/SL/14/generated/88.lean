

theorem Topology.P3_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P3 (Aᶜ) := by
  -- The complement of a closed set is open.
  have h_open : IsOpen (Aᶜ) := by
    simpa using hA_closed.isOpen_compl
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := Aᶜ) h_open