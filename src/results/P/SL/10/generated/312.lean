

theorem Topology.closure_diff_subset_boundary {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ A ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hxCl, hxNotA⟩
  have hxNotInt : x ∉ interior A := by
    intro hxInt
    exact hxNotA (interior_subset hxInt)
  exact And.intro hxCl hxNotInt