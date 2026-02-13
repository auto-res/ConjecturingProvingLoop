

theorem interior_subset_interiorClosureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior (closure A))) := by
  intro x hx
  -- Step 1: upgrade `hx` to membership in `interior (closure A)`.
  have hx₁ : x ∈ interior (closure A) := by
    have h₁ : interior A ⊆ interior (closure A) :=
      interior_subset_interiorClosure (X := X) (A := A)
    exact h₁ hx
  -- Step 2: show `interior (closure A)` is contained in the larger interior.
  have h₂ :
      interior (closure A) ⊆ interior (closure (interior (closure A))) := by
    have h_cl : interior (closure A) ⊆ closure (interior (closure A)) :=
      subset_closure
    have h_open : IsOpen (interior (closure A)) := isOpen_interior
    exact interior_maximal h_cl h_open
  exact h₂ hx₁