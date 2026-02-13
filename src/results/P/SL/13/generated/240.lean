

theorem Topology.closure_interInterior_subset_inter_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((A ∩ interior B) : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `x` lies in `closure A` because `A ∩ interior B ⊆ A`.
  have hxA : (x : X) ∈ closure A :=
    (closure_mono (Set.inter_subset_left : (A ∩ interior B : Set X) ⊆ A)) hx
  -- `x` lies in `closure B` because `A ∩ interior B ⊆ B`.
  have hxB : (x : X) ∈ closure B := by
    have h_subset : ((A ∩ interior B) : Set X) ⊆ B := by
      intro y hy
      exact (interior_subset : interior B ⊆ B) hy.2
    exact (closure_mono h_subset) hx
  exact ⟨hxA, hxB⟩