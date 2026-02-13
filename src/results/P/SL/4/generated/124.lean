

theorem closed_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A → A = closure (interior A) := by
  intro hP2
  -- From `P2`, we get equality of the two closures.
  have h := Topology.closure_eq_closure_interior_of_P2 (A := A) hP2
  -- Since `A` is closed, its closure is itself.
  simpa [hA.closure_eq] using h