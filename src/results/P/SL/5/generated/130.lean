

theorem interior_closure_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (A : Set X)) ⊆ closure (interior (closure A)) := by
  intro x hx
  -- Every set is contained in the closure of itself.
  exact (subset_closure : (interior (closure (A : Set X)) : Set X) ⊆
    closure (interior (closure (A : Set X)))) hx