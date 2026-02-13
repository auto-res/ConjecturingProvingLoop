

theorem interior_closure_interior_subset_closure_inter_interior_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆
      closure (interior A) ∩ interior (closure A) := by
  intro x hx
  have hx_closure : x ∈ closure (interior A) := interior_subset hx
  have hx_interior : x ∈ interior (closure A) :=
    interior_closure_interior_subset_interior_closure (X := X) (A := A) hx
  exact And.intro hx_closure hx_interior