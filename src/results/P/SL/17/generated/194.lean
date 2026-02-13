

theorem Topology.frontier_subset_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP2 : Topology.P2 A) :
    frontier A ⊆ closure (interior A) := by
  intro x hx
  -- From `x ∈ frontier A`, we know `x ∈ closure A`.
  have hx_closure : x ∈ closure A := hx.1
  -- `P2 A` gives the equality `closure (interior A) = closure A`.
  have h_eq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P2 (A := A) hP2
  -- Rewrite the membership using this equality.
  simpa [h_eq] using hx_closure