

theorem interior_closure_interior_eq_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure (A : Set X)) := by
  apply Set.Subset.antisymm
  ·
    have h₁ :
        interior (closure (interior (closure (A : Set X))))
          ⊆ interior (closure (closure (A : Set X))) := by
      simpa using
        (interior_closure_interior_subset_interior_closure
          (A := closure (A : Set X)))
    simpa [closure_closure] using h₁
  ·
    have h₂ :
        interior (closure (A : Set X)) ⊆
          closure (interior (closure (A : Set X))) :=
      subset_closure
    have h₃ := interior_mono h₂
    simpa [interior_interior] using h₃