

theorem interior_closure_interior_eq_self_of_open
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    interior (closure (interior A)) = closure (interior A) := by
  simpa using hOpen.interior_eq