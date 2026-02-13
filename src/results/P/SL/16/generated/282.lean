

theorem Topology.isClosed_closure_diff_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure A \ interior A : Set X) := by
  -- `closure A` is closed.
  have hClosedClosure : IsClosed (closure A) := isClosed_closure
  -- The complement of the open set `interior A` is closed.
  have hClosedComplInt : IsClosed ((interior A)ᶜ) := by
    simpa using (isClosed_compl_iff).2 (isOpen_interior (A := A))
  -- Express the difference as an intersection and use `IsClosed.inter`.
  simpa [Set.diff_eq] using hClosedClosure.inter hClosedComplInt