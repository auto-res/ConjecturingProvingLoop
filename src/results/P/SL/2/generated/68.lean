

theorem Topology.isClosed_P2_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → (Topology.P2 A ↔ IsOpen A) := by
  intro hClosed
  constructor
  · intro hP2
    exact Topology.isClosed_P2_implies_isOpen (A := A) hClosed hP2
  · intro hOpen
    have hP3 : Topology.P3 A := Topology.isOpen_implies_P3 (A := A) hOpen
    exact Topology.isClosed_P3_implies_P2 (A := A) hClosed hP3