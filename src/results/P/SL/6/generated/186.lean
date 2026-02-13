

theorem closure_interior_eq_self_of_P3_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- First, `interior A = A` because `A` is closed and satisfies `P3`.
  have hInt : interior (A : Set X) = A :=
    interior_eq_self_of_P3_closed (A := A) hA_closed hP3
  -- Taking closures and rewriting yields the desired equality.
  simpa [hInt, hA_closed.closure_eq]