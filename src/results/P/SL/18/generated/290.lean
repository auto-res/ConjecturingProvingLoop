

theorem interior_closure_inter_eq_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    interior (closure (A ∩ B : Set X)) = interior (A ∩ B : Set X) := by
  -- The intersection of two closed sets is closed.
  have hClosed : IsClosed (A ∩ B : Set X) := hA_closed.inter hB_closed
  -- For a closed set, its closure equals the set itself.
  simpa [hClosed.closure_eq]