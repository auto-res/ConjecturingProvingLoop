

theorem closure_interior_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    closure (interior (A : Set X)) = closure A := by
  simpa [hA.interior_eq]