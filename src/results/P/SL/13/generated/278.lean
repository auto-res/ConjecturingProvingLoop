

theorem Topology.isClosed_boundaryInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior (A : Set X)) \ interior A) := by
  -- `closure (interior A)` is closed.
  have h_closed_closure : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- The complement of the open set `interior A` is closed.
  have h_closed_compl : IsClosed ((interior (A : Set X))ᶜ) :=
    (isOpen_interior : IsOpen (interior (A : Set X))).isClosed_compl
  -- The desired set is the intersection of two closed sets.
  simpa [Set.diff_eq] using h_closed_closure.inter h_closed_compl