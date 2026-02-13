

theorem interior_closure_interior_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  intro x hx
  have hx_closure : x ∈ closure (interior A) := interior_subset hx
  have h_sub : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_interior_subset_closure_interior_closure (A := A)
  exact h_sub hx_closure