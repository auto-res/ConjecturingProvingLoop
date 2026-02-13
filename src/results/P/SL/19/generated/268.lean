

theorem Topology.closure_interior_diff_interior_closure_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior (closure A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClosInt, hxNotIntClos⟩
  -- From `x ∈ closure (interior A)` we deduce `x ∈ closure A`.
  have hxClosA : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (A := A)) hxClosInt
  -- Since `interior A ⊆ interior (closure A)`, the non-membership
  -- `x ∉ interior (closure A)` implies `x ∉ interior A`.
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    have : x ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (A := A)) hxIntA
    exact hxNotIntClos this
  -- Assemble the two facts to obtain `x ∈ frontier A`.
  exact And.intro hxClosA hxNotIntA