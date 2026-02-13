

theorem Topology.closure_interior_diff_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior A ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClosInt, hxNotInt⟩
  have hxClos : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (A := A)) hxClosInt
  exact And.intro hxClos hxNotInt