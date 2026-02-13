

theorem interior_eq_self_of_P3_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (A : Set X) → interior (A : Set X) = A := by
  intro hP3
  -- A closed set satisfying `P3` is also open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.open_of_P3_closed (A := A) hA) hP3
  -- For an open set, its interior is the set itself.
  simpa using hOpen.interior_eq