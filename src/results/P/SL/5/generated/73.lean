

theorem closure_interior_eq_self_of_closed_and_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    closure (interior A) = A := by
  -- Use the equality given by `P3` and rewrite with closedness of `A`.
  have h :=
    Topology.closure_eq_closure_interior_closure_of_P3 (X := X) (A := A) hP3
  have h' : (A : Set X) = closure (interior A) := by
    simpa [hClosed.closure_eq] using h
  simpa using h'.symm