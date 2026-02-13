

theorem interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Dense (A : Set X)) :
    interior (closure (A : Set X)) = (Set.univ : Set X) := by
  simpa [hA.closure_eq] using
    (by
      simp : interior (Set.univ : Set X) = (Set.univ : Set X))