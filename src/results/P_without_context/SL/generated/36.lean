

theorem Topology.P2_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  -- closure (interior A) ⊆ closure A
  have h_closure_subset : closure (interior (A : Set X)) ⊆ closure A := by
    apply closure_mono
    exact interior_subset
  -- interior (closure (interior A)) ⊆ interior (closure A)
  have h_inter_subset :
      interior (closure (interior (A : Set X))) ⊆ interior (closure A) := by
    apply interior_mono
    exact h_closure_subset
  -- Combine the inclusions
  exact subset_trans hP2 h_inter_subset