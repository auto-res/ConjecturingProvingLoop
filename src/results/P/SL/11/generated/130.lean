

theorem interior_eq_self_of_closed_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 A) :
    interior A = A := by
  -- A closed set satisfying `P2` is necessarily open.
  have hOpen : IsOpen A := isOpen_of_closed_of_P2 (A := A) hClosed hP2
  -- For an open set, the interior is the set itself.
  simpa using hOpen.interior_eq