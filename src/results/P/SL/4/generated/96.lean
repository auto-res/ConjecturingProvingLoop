

theorem interior_closure_eq_of_closure_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : closure A = closure B) :
    interior (closure A) = interior (closure B) := by
  simpa [h]