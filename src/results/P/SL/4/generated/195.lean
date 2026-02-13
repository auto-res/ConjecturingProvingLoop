

theorem closure_inter_interior_eq_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A ∩ interior A) = closure (interior A) := by
  apply subset_antisymm
  · -- `A ∩ interior A` is contained in `interior A`
    have h₁ : (A ∩ interior A : Set X) ⊆ interior A := by
      intro x hx
      exact hx.2
    -- Taking closures preserves inclusions
    exact closure_mono h₁
  · -- `interior A` is contained in `A ∩ interior A`
    have h₂ : (interior A : Set X) ⊆ A ∩ interior A := by
      intro x hx
      exact And.intro (interior_subset hx) hx
    -- Taking closures preserves inclusions
    exact closure_mono h₂