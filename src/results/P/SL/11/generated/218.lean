

theorem P1_of_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 A) :
    Topology.P1 A := by
  -- A closed set satisfying `P3` is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_closed_of_P3 (A := A) hClosed hP3
  -- Every open set satisfies `P1`.
  exact Topology.P1_of_open (A := A) hOpen