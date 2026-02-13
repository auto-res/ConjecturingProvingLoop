

theorem closure_interior_closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  ·
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    simpa [closure_closure] using closure_mono h₁
  ·
    have h₂ : interior A ⊆ interior (closure (interior A)) := by
      have h : interior (interior A) ⊆ interior (closure (interior A)) := by
        have : (interior A : Set X) ⊆ closure (interior A) := subset_closure
        exact interior_mono this
      simpa [interior_interior] using h
    simpa [closure_closure] using closure_mono h₂