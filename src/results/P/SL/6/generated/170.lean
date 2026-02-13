

theorem interior_closure_eq_self_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    interior (closure (A : Set X)) = closure A := by
  simpa using hOpen.interior_eq