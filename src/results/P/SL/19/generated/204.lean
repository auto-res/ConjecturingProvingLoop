

theorem Topology.interior_closure_diff_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) \ interior A ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxIntClos, hxNotIntA⟩
  have hxClosA : x ∈ closure A :=
    (interior_subset : interior (closure A) ⊆ closure A) hxIntClos
  exact And.intro hxClosA hxNotIntA