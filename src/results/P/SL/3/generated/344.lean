

theorem interior_closure_eq_closure_of_isOpen_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hOpen : IsOpen (closure (A : Set X))) :
    interior (closure (A : Set X)) = closure (A : Set X) := by
  simpa using hOpen.interior_eq