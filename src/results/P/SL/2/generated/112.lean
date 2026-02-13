

theorem Topology.P2_implies_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → (A : Set X) ⊆ interior (closure (A : Set X)) := by
  intro hP2
  exact Topology.P2_implies_P3 (A := A) hP2