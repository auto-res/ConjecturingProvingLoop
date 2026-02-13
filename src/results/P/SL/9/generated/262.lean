

theorem Topology.frontier_interior_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) ⊆ closure A := by
  intro x hx
  -- `hx.1` gives `x ∈ closure (interior A)`.
  have hx_closureInt : x ∈ closure (interior A) := hx.1
  -- Since `interior A ⊆ A`, taking closures yields the desired inclusion.
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  exact h_subset hx_closureInt