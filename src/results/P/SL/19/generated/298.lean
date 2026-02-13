

theorem Topology.diff_interior_subset_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    A \ interior A ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxA, hxNotInt⟩
  have hxClos : x ∈ closure A := subset_closure hxA
  exact And.intro hxClos hxNotInt