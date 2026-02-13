

theorem Topology.interior_closure_diff_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) \ A ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxIntClos, hxNotA⟩
  -- `x ∈ closure A` because `interior (closure A) ⊆ closure A`
  have hxClos : x ∈ closure A :=
    (interior_subset : interior (closure A) ⊆ closure A) hxIntClos
  -- `x ∉ interior A` since `interior A ⊆ A`
  have hxNotInt : x ∉ interior A := by
    intro hxIntA
    have : (x : X) ∈ A := interior_subset hxIntA
    exact hxNotA this
  exact And.intro hxClos hxNotInt