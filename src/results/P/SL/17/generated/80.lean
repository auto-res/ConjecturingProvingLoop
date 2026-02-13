

theorem Topology.P1_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) : Topology.P1 A := by
  -- First, deduce that `A` is open from its being closed and satisfying `P2`.
  have hA_open : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  -- Every open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := A) hA_open