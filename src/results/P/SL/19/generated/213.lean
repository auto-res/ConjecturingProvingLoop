

theorem Topology.interior_subset_diff_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ A \ frontier A := by
  intro x hxInt
  have hxA : x ∈ A := interior_subset hxInt
  have hxNotFront : x ∉ frontier A := by
    intro hxFront
    have hNotInt : x ∉ interior A := hxFront.2
    exact hNotInt hxInt
  exact And.intro hxA hxNotFront