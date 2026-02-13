

theorem interior_closure_inter_eq_inter_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    interior (closure (A ∩ B)) = interior A ∩ interior B := by
  -- `A ∩ B` is closed because both `A` and `B` are closed.
  have hABclosed : IsClosed (A ∩ B) := hA.inter hB
  -- Hence its closure is itself.
  have h_closure : closure (A ∩ B) = A ∩ B := hABclosed.closure_eq
  -- Rewrite and use the distributivity of `interior` over intersections.
  simpa [h_closure, interior_inter]