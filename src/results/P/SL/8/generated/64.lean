

theorem closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₁' :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) := closure_mono h₁
    simpa [closure_closure] using h₁'
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) := by
      have h :=
        closure_interior_subset_closure_interior_closure
          (X := X) (A := interior A)
      simpa [interior_interior] using h
    exact h₂