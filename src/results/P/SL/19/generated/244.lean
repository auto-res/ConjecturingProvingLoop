

theorem Topology.closure_diff_interiorClosure_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ interior (closure A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClos, hxNotIntClos⟩
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    have : x ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (A := A)) hxIntA
    exact hxNotIntClos this
  exact And.intro hxClos hxNotIntA