

theorem Topology.isClosed_closure_diff_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) : IsClosed (closure A \ interior A) := by
  have h_closed_closure : IsClosed (closure A) := isClosed_closure
  have h_closed_compl : IsClosed ((interior A)ᶜ) :=
    (isOpen_interior : IsOpen (interior A)).isClosed_compl
  simpa [Set.diff_eq] using IsClosed.inter h_closed_closure h_closed_compl