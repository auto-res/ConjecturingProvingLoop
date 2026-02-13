

theorem P1_congr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (A : Set X) = B) : Topology.P1 A ↔ Topology.P1 B := by
  simpa [h]