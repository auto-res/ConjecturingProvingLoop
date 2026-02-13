

theorem Topology.closure_interior_inter_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ∩ interior (closure A) ⊆ closure A := by
  intro x hx
  -- The first component of `hx` already lies in `closure A`.
  exact (Topology.closure_interior_subset_closure (X := X) (A := A)) hx.1