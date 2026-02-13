

theorem closure_interior_eq_self_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P3 A → closure (interior (A : Set X)) = A := by
  intro hP3
  -- From `P3` and closedness, deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    ((Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1) hP3
  -- A clopen set satisfies `closure (interior A) = A`.
  exact
    Topology.closure_interior_eq_self_of_clopen
      (X := X) (A := A) hOpen hClosed