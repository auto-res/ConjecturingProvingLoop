

theorem Topology.interiorClosure_union_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    interior (closure (A ∪ B : Set X)) = interior (A ∪ B) := by
  -- Since `A ∪ B` is closed, its closure coincides with itself.
  have hClosure : closure (A ∪ B : Set X) = A ∪ B :=
    (IsClosed.union hA hB).closure_eq
  -- Rewriting with `hClosure` gives the desired equality.
  simpa [hClosure]