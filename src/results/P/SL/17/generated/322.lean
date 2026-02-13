

theorem Topology.closure_interior_diff_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} : closure (interior A) \ A ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClInt, hxNotA⟩
  -- `x` lies in `closure A` because `closure (interior A) ⊆ closure A`.
  have hxClA : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (A := A)) hxClInt
  -- `x` is not in `interior A` since it is not in `A`.
  have hxNotInt : x ∉ interior A := by
    intro hInt
    have : x ∈ A := interior_subset hInt
    exact hxNotA this
  -- Assemble the frontier membership.
  exact And.intro hxClA hxNotInt