

theorem Topology.interiorClosureInterior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- Show membership in `interior (closure (interior A))`.
  have hA : x ∈ interior (closure (interior A)) := by
    have hSub : interior (closure (interior (A ∩ B))) ⊆
        interior (closure (interior A)) := by
      apply interior_mono
      apply closure_mono
      apply interior_mono
      exact Set.inter_subset_left
    exact hSub hx
  -- Show membership in `interior (closure (interior B))`.
  have hB : x ∈ interior (closure (interior B)) := by
    have hSub : interior (closure (interior (A ∩ B))) ⊆
        interior (closure (interior B)) := by
      apply interior_mono
      apply closure_mono
      apply interior_mono
      exact Set.inter_subset_right
    exact hSub hx
  exact ⟨hA, hB⟩