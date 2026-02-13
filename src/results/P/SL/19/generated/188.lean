

theorem Topology.frontier_interior_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (interior A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClosInt, hxNotIntInt⟩
  have hxClosA : x ∈ closure A := by
    have hSub : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (A := A)
    exact hSub hxClosInt
  have hxNotIntA : x ∉ interior A := by
    simpa [interior_interior] using hxNotIntInt
  exact And.intro hxClosA hxNotIntA