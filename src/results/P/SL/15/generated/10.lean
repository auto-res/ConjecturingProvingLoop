

theorem interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  intro x hx
  have h_mono : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono (subset_closure)
  have h_eq : interior (interior A) = interior A := by
    simpa using (isOpen_interior (A := A)).interior_eq
  have hx' : x ∈ interior (interior A) := by
    simpa [h_eq] using hx
  exact h_mono hx'