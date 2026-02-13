

theorem Topology.closure_interior_inter_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∩ closure A = closure (interior A) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hx_ci
    have hx_cl : x ∈ closure A :=
      (Topology.closure_interior_subset_closure (A := A)) hx_ci
    exact And.intro hx_ci hx_cl