

theorem Topology.closure_diff_interior_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (A \ interior A) = A \ interior A := by
  -- First, show that `A \ interior A` is closed.
  have h_closed : IsClosed (A \ interior A) := by
    -- The complement of the open set `interior A` is closed.
    have h_compl_closed : IsClosed ((interior A)ᶜ) :=
      (isOpen_interior : IsOpen (interior A)).isClosed_compl
    -- An intersection of two closed sets is closed.
    simpa [Set.diff_eq] using IsClosed.inter hA h_compl_closed
  -- The closure of a closed set is itself.
  simpa [h_closed.closure_eq]