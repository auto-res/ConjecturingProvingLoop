

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior A)) ⊆ closure A := by
  intro x hx
  have hx_closure : x ∈ closure (interior A) := interior_subset hx
  have h_closure_subset : closure (interior A) ⊆ closure A := by
    have h_int_subset : interior A ⊆ A := interior_subset
    exact closure_mono h_int_subset
  exact h_closure_subset hx_closure