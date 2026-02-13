

theorem P3_and_P2_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P3 (A : Set X) ∧ Topology.P2 A) ↔ Topology.P2 A := by
  constructor
  · intro h
    exact h.2
  · intro hP2
    exact And.intro (Topology.P2_implies_P3 (A := A) hP2) hP2