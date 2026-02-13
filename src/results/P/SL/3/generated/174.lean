

theorem closure_interior_eq_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- From `P3` and the fact that `A` is closed, deduce `P2`.
  have hP2 : Topology.P2 (A : Set X) :=
    Topology.P2_of_isClosed_and_P3 (A := A) hA_closed hP3
  -- Apply the existing result that relates `P2`, closedness, and the desired equality.
  exact closure_interior_eq_of_isClosed_and_P2 (A := A) hA_closed hP2