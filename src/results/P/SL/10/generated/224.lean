

theorem Topology.closure_inter_subset_closed_left
    {X : Type*} [TopologicalSpace X] {U A : Set X} (hU : IsClosed U) :
    closure (U ∩ A) ⊆ U := by
  have h_subset : closure (U ∩ A) ⊆ closure U :=
    closure_mono (Set.inter_subset_left : (U ∩ A) ⊆ U)
  simpa [hU.closure_eq] using h_subset