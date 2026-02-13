

theorem Topology.frontier_subset_closure_interior_of_subset_P2
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP2B : Topology.P2 B) :
    frontier A ⊆ closure (interior B) := by
  intro x hx
  -- From `x ∈ frontier A`, we get `x ∈ closure A`.
  have hx_clA : x ∈ closure A := hx.1
  -- Using the inclusion `A ⊆ B`, deduce `x ∈ closure B`.
  have hx_clB : x ∈ closure B := (closure_mono hAB) hx_clA
  -- For a set satisfying `P2`, its two closures coincide.
  have h_eq : closure (interior B) = closure B :=
    Topology.closure_interior_eq_closure_of_P2 (A := B) hP2B
  -- Rewrite and conclude.
  simpa [h_eq] using hx_clB