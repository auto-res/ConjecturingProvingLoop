

theorem closure_interior_inter_interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∩ interior (closure A) ⊆
      closure (interior (closure A)) := by
  intro x hx
  -- `x` lies in `closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hx.1
  -- And `closure (interior A)` is contained in `closure (interior (closure A))`.
  have hsubset :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closure_interior_subset_closure_interior_closure (X := X) A
  -- Combining the two facts yields the desired membership.
  exact hsubset hx_cl