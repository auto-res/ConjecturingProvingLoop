

theorem Topology.interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  intro x hx
  have hx_int_cl : x ∈ interior (closure A) :=
    (Topology.interior_subset_interior_closure (X := X) (A := A)) hx
  exact subset_closure hx_int_cl