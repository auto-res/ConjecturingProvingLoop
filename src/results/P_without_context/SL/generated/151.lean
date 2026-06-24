

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 (X := X) A := by
  intro hP2
  unfold Topology.P2 at hP2
  unfold Topology.P3
  refine Set.Subset.trans hP2 ?_
  have h₁ : closure (interior A) ⊆ closure A := by
    exact closure_mono interior_subset
  exact interior_mono h₁