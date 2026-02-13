

theorem interior_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  intro x hx
  -- First, move from `interior A` to `interior (closure A)`.
  have hx₁ : x ∈ interior (closure A) :=
    (interior_subset_interiorClosure (X := X) (A := A)) hx
  -- Then, use the fact that any set is contained in the closure of itself.
  have hx₂ : x ∈ closure (interior (closure A)) :=
    (subset_closure : interior (closure A) ⊆
      closure (interior (closure A))) hx₁
  exact hx₂