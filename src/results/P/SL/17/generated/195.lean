

theorem Topology.frontier_subset_closure_interior_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) :
    frontier A ⊆ closure (interior (closure A)) := by
  intro x hx
  have hx_closure : x ∈ closure A := hx.1
  have h_eq :
      closure (interior (closure A)) = closure A :=
    Topology.closure_interior_closure_eq_closure_of_P3 (A := A) hP3
  simpa [h_eq] using hx_closure