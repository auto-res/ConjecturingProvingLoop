

theorem Topology.P3_congr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A = B) :
    Topology.P3 A ↔ Topology.P3 B := by
  cases h
  rfl