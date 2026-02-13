

theorem interior_closure_eq_self_of_isOpen_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen (closure (A : Set X)) →
      interior (closure (A : Set X)) = closure (A : Set X) := by
  intro hOpen
  simpa using hOpen.interior_eq