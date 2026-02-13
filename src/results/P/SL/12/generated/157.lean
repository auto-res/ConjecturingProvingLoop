

theorem Topology.closure_inter_subset_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure A := by
    have h_sub : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
    exact (closure_mono h_sub) hx
  have hxB : x ∈ closure B := by
    have h_sub : (A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    exact (closure_mono h_sub) hx
  exact And.intro hxA hxB