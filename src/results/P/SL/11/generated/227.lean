

theorem interior_closure_eq_closure_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    interior (closure A) = closure A := by
  simpa using hOpen.interior_eq