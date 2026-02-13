

theorem Topology.isClosed_isOpen_implies_P1_P2_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → IsOpen A → (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) := by
  intro hClosed hOpen
  have hEquiv := (Topology.isClosed_isOpen_iff_P1_P2_P3 (A := A) hClosed)
  exact (hEquiv).1 hOpen