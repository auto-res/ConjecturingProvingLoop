

theorem Topology.frontier_closure_subset_frontier
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (closure (A : Set X)) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hx_cl_cl, hx_not_int_cl⟩
  -- `x` lies in the closure of `A`.
  have hx_cl : x ∈ closure (A : Set X) := by
    simpa [closure_closure] using hx_cl_cl
  -- Show that `x` is not in the interior of `A`.
  have hx_not_int : x ∉ interior (A : Set X) := by
    intro hx_int
    have : x ∈ interior (closure (A : Set X)) :=
      (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx_int
    exact hx_not_int_cl this
  exact ⟨hx_cl, hx_not_int⟩