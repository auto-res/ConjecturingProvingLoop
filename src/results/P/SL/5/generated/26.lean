

theorem interior_closure_interior_subset_closure_interior_and_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ closure (interior A) ∩ interior (closure A) := by
  intro x hx
  have h_closure : x ∈ closure (interior A) := interior_subset hx
  have hsub : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  have h_interior : x ∈ interior (closure A) := (interior_mono hsub) hx
  exact ⟨h_closure, h_interior⟩