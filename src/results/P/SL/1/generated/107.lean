

theorem Topology.P1_of_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  -- From `P2` and closedness, we deduce that `A` is open.
  have hOpen : IsOpen A := Topology.isOpen_of_P2_of_isClosed (A := A) hA hP2
  -- Every open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := A) hOpen