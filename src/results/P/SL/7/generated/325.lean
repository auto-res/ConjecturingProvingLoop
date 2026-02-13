

theorem Topology.P2_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A ⊆ interior (closure A) := by
  intro hP2
  exact (Topology.P2_implies_P3 (A := A) hP2)