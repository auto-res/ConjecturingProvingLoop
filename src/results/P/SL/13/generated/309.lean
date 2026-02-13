

theorem Topology.boundary_empty_of_closed_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_closed : IsClosed (A : Set X)) (h_dense : Dense (A : Set X)) :
    closure (A : Set X) \ interior A = (∅ : Set X) := by
  -- A closed and dense set is the whole space.
  have h_eq_univ : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (X := X) (A := A) h_closed h_dense
  -- Rewrite both the closure and the interior using `h_eq_univ`.
  have h_closure_eq : closure (A : Set X) = (Set.univ : Set X) := by
    simpa [h_eq_univ, closure_univ] using (h_closed.closure_eq)
  have h_interior_eq : interior (A : Set X) = (Set.univ : Set X) := by
    simpa [h_eq_univ, interior_univ] using
      (isOpen_univ.interior_eq.symm.trans (by simp [h_eq_univ]))
  -- Compute the boundary using these equalities.
  simpa [h_closure_eq, h_interior_eq, Set.diff_self]