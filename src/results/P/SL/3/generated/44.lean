

theorem closure_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (A : Set X)))) =
      closure (interior (A : Set X)) := by
  apply Set.Subset.antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h₁ :
        interior (closure (interior (A : Set X))) ⊆
          closure (interior (A : Set X)) := by
      -- `interior S` is always contained in `S`
      exact interior_subset (s := closure (interior (A : Set X)))
    have h₂ :
        closure (interior (closure (interior (A : Set X)))) ⊆
          closure (closure (interior (A : Set X))) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h₁ :
        interior (A : Set X) ⊆
          interior (closure (interior (A : Set X))) := by
      apply interior_maximal
      · exact subset_closure
      · exact isOpen_interior
    have h₂ :
        closure (interior (A : Set X)) ⊆
          closure (interior (closure (interior (A : Set X)))) :=
      closure_mono h₁
    simpa using h₂