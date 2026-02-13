

theorem interior_closure_interior_subset_closure_inter_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ closure A ∩ interior (closure A) := by
  intro x hx
  have h_cl : x ∈ closure A :=
    interior_closure_interior_subset_closure (X := X) (A := A) hx
  have h_int : x ∈ interior (closure A) :=
    interior_closure_interior_subset_interior_closure (X := X) (A := A) hx
  exact And.intro h_cl h_int