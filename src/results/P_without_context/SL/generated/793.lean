

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  have h_incl : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h1 : interior A ⊆ (A : Set X) := interior_subset
    have h2 : closure (interior A) ⊆ closure (A : Set X) := closure_mono h1
    exact interior_mono h2
  exact Set.Subset.trans hP2 h_incl