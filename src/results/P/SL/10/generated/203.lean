

theorem Topology.closure_diff_interior_eq_self_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (A \ interior A) = A \ interior A := by
  -- First, prove the set `A \ interior A` is closed.
  have hClosed : IsClosed (A \ interior A) := by
    -- `A` is closed by hypothesis, and `(interior A)ᶜ` is closed as the complement of an open set.
    have hIntCompl : IsClosed ((interior A)ᶜ) :=
      (isOpen_interior : IsOpen (interior A)).isClosed_compl
    -- The intersection of two closed sets is closed; rewrite the set difference as such an intersection.
    simpa [Set.diff_eq] using hA.inter hIntCompl
  -- The closure of a closed set is itself.
  simpa using hClosed.closure_eq