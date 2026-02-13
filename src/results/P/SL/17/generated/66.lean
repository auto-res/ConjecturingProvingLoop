

theorem Topology.P1_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  -- A closed set satisfying `P3` is open
  have hA_open : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  -- Every open set satisfies `P1`
  exact Topology.P1_of_isOpen (A := A) hA_open