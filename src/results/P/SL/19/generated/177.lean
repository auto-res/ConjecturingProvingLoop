

theorem Topology.frontier_closure_subset_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure A) ⊆ frontier A := by
  intro x hx
  -- Expand the membership condition in the frontier of `closure A`.
  rcases hx with ⟨hxClosClosA, hxNotIntClosA⟩
  -- Since `closure (closure A) = closure A`, we already have `x ∈ closure A`.
  have hxClosA : x ∈ closure A := by
    simpa [closure_closure] using hxClosClosA
  -- Show that `x ∉ interior A` using the fact that
  -- `interior A ⊆ interior (closure A)`.
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    have : (x : X) ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (A := A)) hxIntA
    exact hxNotIntClosA this
  -- Conclude that `x ∈ frontier A`.
  exact And.intro hxClosA hxNotIntA