

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 (A : Set X) := by
  intro hP2 x hxA
  exact interior_subset (hP2 hxA)