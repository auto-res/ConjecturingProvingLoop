

theorem Topology.P2_congr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A = B) :
    Topology.P2 A ↔ Topology.P2 B := by
  cases h
  rfl