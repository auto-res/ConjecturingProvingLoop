

theorem Topology.closure_diff_closure_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ closure (interior A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClosA, hxNotClosInt⟩
  have hxNotInt : x ∉ interior A := by
    intro hxInt
    have : (x : X) ∈ closure (interior A) := subset_closure hxInt
    exact hxNotClosInt this
  exact And.intro hxClosA hxNotInt