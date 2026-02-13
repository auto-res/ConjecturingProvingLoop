

theorem Topology.interior_closure_union_eq_interior_union_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    interior (closure (A ∪ B)) = interior (A ∪ B) := by
  -- The union of two closed sets is closed.
  have hClosedUnion : IsClosed (A ∪ B : Set X) := hA.union hB
  -- For a closed set, its closure is itself.
  have hClosureEq : closure (A ∪ B : Set X) = A ∪ B := hClosedUnion.closure_eq
  -- Rewrite using the equality obtained above.
  simpa [hClosureEq]