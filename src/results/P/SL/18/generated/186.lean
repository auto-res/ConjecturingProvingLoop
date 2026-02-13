

theorem dense_interior_iff_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) ↔
      closure (interior (A : Set X)) = Set.univ := by
  simpa using
    (dense_iff_closure_eq_univ (A := interior (A : Set X)))