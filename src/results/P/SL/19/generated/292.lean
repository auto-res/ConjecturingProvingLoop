

theorem Topology.interior_closure_diff_closure_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) \ closure (interior A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxIntClos, hxNotClosInt⟩
  -- `x ∈ closure A` because `interior (closure A) ⊆ closure A`.
  have hxClosA : x ∈ closure A :=
    (interior_subset : interior (closure A) ⊆ closure A) hxIntClos
  -- We show `x ∉ interior A` using the assumption `x ∉ closure (interior A)`.
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    have : x ∈ closure (interior A) := subset_closure hxIntA
    exact hxNotClosInt this
  -- Assemble the two facts to obtain membership in the frontier.
  exact And.intro hxClosA hxNotIntA