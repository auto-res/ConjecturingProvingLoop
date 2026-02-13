

theorem closure_interior_eq_self_of_clopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- Since `A` is open, its interior is itself.
  have hInt : interior (A : Set X) = A := hOpen.interior_eq
  -- Taking closures and rewriting via `hInt`.
  have hClos : closure (interior (A : Set X)) = closure A := by
    simpa [hInt]
  -- As `A` is closed, its closure is itself.
  simpa [hClosed.closure_eq] using hClos