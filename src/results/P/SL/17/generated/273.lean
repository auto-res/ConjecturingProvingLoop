

theorem Topology.closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `x` lies in `closure A` because `A ∩ interior B ⊆ A`.
  have hxA : x ∈ closure A := by
    have h_subset : (A ∩ interior B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono h_subset) hx
  -- `x` lies in `closure B` because `interior B ⊆ B`.
  have hxB : x ∈ closure B := by
    have h_subset : (A ∩ interior B : Set X) ⊆ B := by
      intro y hy
      exact interior_subset hy.2
    exact (closure_mono h_subset) hx
  exact And.intro hxA hxB