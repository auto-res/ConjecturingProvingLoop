

theorem closure_interior_eq_self_of_P2_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) → closure (interior A) = A := by
  intro hP2
  -- `interior A = A` because `A` is closed and satisfies `P2`.
  have hInt : interior A = A :=
    (interior_eq_self_of_P2_closed (A := A) hA) hP2
  -- Apply `closure` to both sides and rewrite using `hA.closure_eq`.
  have hClos : closure (interior A) = closure A :=
    congrArg closure hInt
  simpa [hA.closure_eq] using hClos