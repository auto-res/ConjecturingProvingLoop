

theorem Topology.closure_diff_closureInterior_subset_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) \ closure (interior A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hx_cl, hx_not_cl_int⟩
  have hx_not_int : x ∉ interior A := by
    intro hx_int
    have : x ∈ closure (interior A) := subset_closure hx_int
    exact hx_not_cl_int this
  exact ⟨hx_cl, hx_not_int⟩