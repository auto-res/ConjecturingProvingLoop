

theorem Topology.isClosed_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure A \ interior A) := by
  -- `closure A` is closed.
  have hClosedCl : IsClosed (closure A) := isClosed_closure
  -- The complement of an open set is closed.
  have hClosedCompl : IsClosed ((interior A)ᶜ) :=
    (isOpen_interior : IsOpen (interior A)).isClosed_compl
  -- Rewrite the set difference as an intersection and use `IsClosed.inter`.
  simpa [Set.diff_eq] using hClosedCl.inter hClosedCompl