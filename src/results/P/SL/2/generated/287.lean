

theorem Topology.isClosed_P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P2 A → Topology.P1 A := by
  intro hClosed hP2
  -- From the assumptions we first obtain that `A` is open.
  have hOpen : IsOpen A :=
    Topology.isClosed_P2_implies_isOpen (A := A) hClosed hP2
  -- Every open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (A := A) hOpen