

theorem Topology.closure_diff_subset_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ A ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClos, hxNotA⟩
  have hxNotInt : x ∉ interior A := by
    intro hxInt
    exact hxNotA (interior_subset hxInt)
  exact And.intro hxClos hxNotInt