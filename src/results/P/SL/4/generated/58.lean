

theorem interior_closure_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  intro x hx
  -- The closure of a set contains the set itself.
  exact subset_closure hx