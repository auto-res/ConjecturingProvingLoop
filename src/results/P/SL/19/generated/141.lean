

theorem Topology.closure_interior_diff_interior_subset_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior A ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hxClosInt, hxNotInt⟩
  have hxClosA : x ∈ closure A := by
    have hSub : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (A := A)
    exact hSub hxClosInt
  exact And.intro hxClosA hxNotInt