

theorem Topology.closure_compl_eq_compl_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_open : IsOpen (A : Set X)) :
    closure ((A : Set X)ᶜ) = (A : Set X)ᶜ := by
  -- The complement of an open set is closed.
  have h_closed : IsClosed ((A : Set X)ᶜ) := hA_open.isClosed_compl
  -- The closure of a closed set is the set itself.
  simpa using h_closed.closure_eq