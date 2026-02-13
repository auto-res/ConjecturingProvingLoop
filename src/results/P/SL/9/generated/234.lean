

theorem Topology.interiorClosure_diff_closureInterior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) \ closure (interior A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hx_int_cl, hx_not_cl_int⟩
  -- `x` lies in `closure A` because `interior (closure A) ⊆ closure A`.
  have hx_clA : x ∈ closure (A : Set X) := interior_subset hx_int_cl
  -- Show that `x` is not in `interior A`.
  have hx_not_intA : x ∉ interior A := by
    intro hx_intA
    have : x ∈ closure (interior A) := subset_closure hx_intA
    exact hx_not_cl_int this
  exact ⟨hx_clA, hx_not_intA⟩