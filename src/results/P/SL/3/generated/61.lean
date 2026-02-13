

theorem interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) →
      interior (closure (A : Set X)) = Set.univ := by
  intro h_dense
  simpa [h_dense, interior_univ]