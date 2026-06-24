

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h1 : interior A ⊆ A := interior_subset
    have h2 : closure (interior A) ⊆ closure A := closure_mono h1
    exact interior_mono h2
  exact Set.Subset.trans hP2 hsubset