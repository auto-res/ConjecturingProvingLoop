

theorem interior_satisfies_P3 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) := by
  have h : Topology.P2 (interior A) := interior_satisfies_P2 A
  exact P2_implies_P3 h