

theorem Topology.P3_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    Topology.P3 A := by
  -- A closed set satisfying `P2` is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen