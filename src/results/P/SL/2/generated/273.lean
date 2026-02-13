

theorem Topology.frontier_subset_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (A : Set X) → frontier (A : Set X) ⊆ A := by
  intro hClosed x hxFrontier
  -- From `hxFrontier` we obtain `x ∈ closure A`.
  have hx_closure : (x : X) ∈ closure (A : Set X) := hxFrontier.1
  -- Since `A` is closed, `closure A = A`.
  simpa [hClosed.closure_eq] using hx_closure