

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro hA
  unfold Topology.P2 at hA
  unfold Topology.P1
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact subset_trans hA hsubset