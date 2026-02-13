

theorem Topology.closure_interior_diff_interior_closure_subset_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior (closure A) ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hxClosIntA, hxNotIntClosA⟩
  -- `x ∈ closure A` since `closure (interior A) ⊆ closure A`
  have hxClosA : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (A := A)) hxClosIntA
  -- Show `x ∉ interior A` using the assumption `x ∉ interior (closure A)`
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    have : x ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (A := A)) hxIntA
    exact hxNotIntClosA this
  exact And.intro hxClosA hxNotIntA