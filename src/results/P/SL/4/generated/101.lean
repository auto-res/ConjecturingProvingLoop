

theorem closure_interior_closure_interior_eq {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h₁ : interior A ⊆ interior (closure (interior A)) :=
      interior_subset_interior_closure_interior (X := X) (A := A)
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    exact h₂