

theorem closure_interior_eq_self_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 A → closure (interior (A : Set X)) = A := by
  intro hP2
  -- From `P2` and the fact that `A` is closed, deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hClosed) hP2
  -- A clopen set satisfies `closure (interior A) = A`.
  exact
    Topology.closure_interior_eq_self_of_clopen
      (X := X) (A := A) hOpen hClosed