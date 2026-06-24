

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 A := by
  intro hP2
  have h1 : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact subset_trans hP2 h1