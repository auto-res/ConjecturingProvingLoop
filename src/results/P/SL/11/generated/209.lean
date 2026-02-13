

theorem interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    interior (closure A) = (Set.univ : Set X) := by
  simpa [hDense, interior_univ]