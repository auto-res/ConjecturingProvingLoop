

theorem interior_closure_interior_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDenseInt : Dense (interior (A : Set X))) :
    interior (closure (interior (A : Set X))) = Set.univ := by
  simpa using
    (dense_interior_iff_interior_closure_interior_eq_univ (A := A)).1
      hDenseInt