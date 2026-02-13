

theorem Topology.isClosed_P2_implies_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P2 A → IsOpen A := by
  intro hClosed hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact Topology.isClosed_P3_implies_isOpen (A := A) hClosed hP3