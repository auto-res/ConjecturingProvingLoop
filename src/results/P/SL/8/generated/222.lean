

theorem interior_closure_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) :
    interior (closure A) = closure A := by
  simpa using h_open.interior_eq