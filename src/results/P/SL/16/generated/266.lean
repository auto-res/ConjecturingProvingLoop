

theorem Topology.interior_closure_inter_eq_interior_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    interior (closure (A ∩ B)) = interior (A ∩ B) := by
  -- Since both `A` and `B` are closed, so is their intersection.
  have hClosed : IsClosed (A ∩ B : Set X) := hA.inter hB
  -- For a closed set, its closure is itself.
  have h_closure_eq : closure (A ∩ B : Set X) = A ∩ B := hClosed.closure_eq
  -- Rewrite using the obtained equality.
  simpa [h_closure_eq]