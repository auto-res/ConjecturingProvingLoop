

theorem interior_closure_eq_univ_of_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : closure (A : Set X) = (Set.univ : Set X)) :
    interior (closure (A : Set X)) = Set.univ := by
  simpa [hA, interior_univ]