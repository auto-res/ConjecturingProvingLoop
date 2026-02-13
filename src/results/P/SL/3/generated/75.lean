

theorem Topology.P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 A ↔ IsOpen (A : Set X) := by
  constructor
  · intro hP2
    -- From `P2` we get `P3`.
    have hP3 : Topology.P3 (A : Set X) :=
      Topology.P2_implies_P3 (A := A) hP2
    -- A closed set satisfying `P3` is open.
    exact isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  · intro hOpen
    -- An open set automatically satisfies `P2`.
    exact Topology.P2_of_isOpen (A := A) hOpen