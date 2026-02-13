

theorem Topology.interior_closure_diff_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) \ interior (A : Set X) ⊆
      frontier (A : Set X) := by
  intro x hx
  rcases hx with ⟨hxIntCl, hxNotIntA⟩
  have hxCl : (x : X) ∈ closure (A : Set X) := interior_subset hxIntCl
  exact And.intro hxCl hxNotIntA