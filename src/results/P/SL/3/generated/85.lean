

theorem interior_closure_interior_eq_univ_iff_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) = (Set.univ : Set X) ↔
      closure (interior (A : Set X)) = (Set.univ : Set X) := by
  simpa using
    (interior_closure_eq_univ_iff_dense
      (A := interior (A : Set X)))