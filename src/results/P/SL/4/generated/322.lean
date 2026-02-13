

theorem frontier_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → frontier (A : Set X) ⊆ closure (interior A) := by
  intro hP1
  intro x hxFront
  -- `hxFront` gives `x ∈ closure A`.
  have hx_cl : x ∈ closure A := hxFront.1
  -- Under `P1`, the two closures coincide.
  have h_eq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  -- Rewrite and conclude.
  simpa [h_eq] using hx_cl