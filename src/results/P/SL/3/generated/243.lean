

theorem closure_diff_interior_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) \ interior (A : Set X) ⊆ closure (A : Set X) := by
  intro x hx
  exact hx.1