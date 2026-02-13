

theorem P2_congr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (A : Set X) = B) :
    Topology.P2 A ↔ Topology.P2 B := by
  simpa [Topology.P2, h]