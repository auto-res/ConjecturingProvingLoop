

theorem Topology.closureInterior_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hA : closure (interior (A ∩ B)) ⊆ closure (interior A) := by
    apply closure_mono
    apply interior_mono
    exact Set.inter_subset_left
  have hB : closure (interior (A ∩ B)) ⊆ closure (interior B) := by
    apply closure_mono
    apply interior_mono
    exact Set.inter_subset_right
  exact ⟨hA hx, hB hx⟩