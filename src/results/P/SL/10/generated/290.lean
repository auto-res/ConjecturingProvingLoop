

theorem Topology.interior_closure_diff_interior_subset_boundary
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) \ interior A ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hxIntCl, hxNotInt⟩
  have hxCl : x ∈ closure A := interior_subset hxIntCl
  exact And.intro hxCl hxNotInt