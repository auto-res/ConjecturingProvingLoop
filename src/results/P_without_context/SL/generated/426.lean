

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P3]
  have h1 : interior A ⊆ (A : Set X) := interior_subset
  have h2 : closure (interior A) ⊆ closure (A : Set X) := closure_mono h1
  have h3 : interior (closure (interior A)) ⊆ interior (closure A) := interior_mono h2
  exact subset_trans hP2 h3