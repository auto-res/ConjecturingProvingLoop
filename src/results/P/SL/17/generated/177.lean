

theorem Topology.frontier_subset_closure_interior_of_P1 {X : Type*}
    [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) :
    frontier A ⊆ closure (interior A) := by
  intro x hx
  -- From `x ∈ frontier A`, we know `x ∈ closure A`.
  have hx_closure : x ∈ closure A := hx.1
  -- Under `P1`, the two closures coincide.
  have h_eq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (A := A) hP1
  -- Rewrite the membership using this equality.
  simpa [h_eq] using hx_closure