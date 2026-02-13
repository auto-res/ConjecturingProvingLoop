

theorem interior_eq_empty_of_closure_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) = (∅ : Set X) → interior A = (∅ : Set X) := by
  intro h
  ext x
  constructor
  · intro hx
    have : x ∈ closure (interior A) := subset_closure hx
    simpa [h] using this
  · intro hx
    cases hx