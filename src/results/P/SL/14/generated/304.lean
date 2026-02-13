

theorem Topology.clopen_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    IsOpen (closure (A : Set X)) ∧ IsClosed (closure A) := by
  exact ⟨h_open, isClosed_closure⟩