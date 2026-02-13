

theorem frontier_interior_subset_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) ⊆ frontier A := by
  intro x hx
  -- Unpack the definition of membership in the frontier of `interior A`.
  rcases hx with ⟨hx_cl_int, hx_not_int_int⟩
  -- `interior A ⊆ A`, so taking closures yields the corresponding inclusion.
  have hx_closureA : x ∈ closure A := by
    have h_subset : (interior A : Set X) ⊆ A := interior_subset
    exact (closure_mono h_subset) hx_cl_int
  -- `x` is not in `interior (interior A) = interior A`.
  have hx_not_intA : x ∉ interior A := by
    simpa [interior_interior] using hx_not_int_int
  -- Combine the facts to conclude `x ∈ frontier A`.
  exact And.intro hx_closureA hx_not_intA