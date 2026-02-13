

theorem Topology.frontier_interior_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (interior A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨h_clos, h_not_int⟩
  -- `x` lies in the closure of `A` because `interior A ⊆ A`.
  have h_closA : x ∈ closure A :=
    (closure_mono (interior_subset : interior A ⊆ A)) h_clos
  -- `x` is not in the interior of `A`.
  have h_not_intA : x ∉ interior A := by
    simpa [interior_interior] using h_not_int
  exact And.intro h_closA h_not_intA