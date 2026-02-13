

theorem closure_interior_closure_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  ·
    -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆ closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  ·
    -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h₁ : interior A ⊆ interior (closure (interior A)) := by
      -- `interior A` is open and contained in `closure (interior A)`
      have hsub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
      have := interior_mono hsub
      simpa [interior_interior] using this
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    simpa using h₂