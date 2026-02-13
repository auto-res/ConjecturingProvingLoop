

theorem closure_interior_closure_eq_self_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) →
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  intro hOpen
  have hInt : interior (closure (A : Set X)) = closure (A : Set X) := by
    simpa using hOpen.interior_eq
  calc
    closure (interior (closure (A : Set X))) =
        closure (closure (A : Set X)) := by
      simpa [hInt]
    _ = closure (A : Set X) := by
      simpa [closure_closure]