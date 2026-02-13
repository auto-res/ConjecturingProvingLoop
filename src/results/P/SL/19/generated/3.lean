

theorem Topology.interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  intro x hx
  have hx' : x ∈ interior (closure A) :=
    (Topology.interior_closure_interior_subset_interior_closure (A := A)) hx
  exact interior_subset hx'