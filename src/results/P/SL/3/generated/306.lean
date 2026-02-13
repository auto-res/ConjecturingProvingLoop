

theorem interior_closure_interior_eq_interior_of_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    interior (closure (interior (A : Set X))) = interior (A : Set X) := by
  apply Set.Subset.antisymm
  · -- `interior (closure (interior A)) ⊆ interior A`
    have hsubset₁ :
        closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_interior_subset_closure (A := A)
    have hsubset :
        closure (interior (A : Set X)) ⊆ (A : Set X) := by
      simpa [hA_closed.closure_eq] using hsubset₁
    exact interior_mono hsubset
  · -- `interior A ⊆ interior (closure (interior A))`
    exact interior_subset_interior_closure_interior (A := A)