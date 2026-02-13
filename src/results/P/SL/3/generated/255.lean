

theorem boundary_eq_empty_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) := by
  -- A closed set satisfying `P3` is open.
  have hOpen : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P3 (A := A) hClosed hP3
  -- For a clopen set, the boundary is empty.
  simpa using
    (boundary_eq_empty_of_isClopen (A := A) hOpen hClosed)