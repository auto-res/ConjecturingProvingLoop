

theorem interior_closure_interior_eq_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    interior (closure (interior A)) = interior (closure A) := by
  simpa [hA.interior_eq]