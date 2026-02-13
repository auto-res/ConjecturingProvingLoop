

theorem interior_closure_interior_eq_interior_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    interior (closure (interior (A : Set X))) = interior (closure A) := by
  simpa [hA.interior_eq]