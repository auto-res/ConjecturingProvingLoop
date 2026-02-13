

theorem Topology.P1_congr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A = B) :
    Topology.P1 A ↔ Topology.P1 B := by
  cases h
  rfl