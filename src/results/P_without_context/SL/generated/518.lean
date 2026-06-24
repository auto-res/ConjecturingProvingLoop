

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := by
      exact closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono hcl
  exact Set.Subset.trans hP2 hmono