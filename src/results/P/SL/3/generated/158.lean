

theorem interior_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (interior (closure (A : Set X))) = interior (closure (A : Set X)) := by
  simpa [interior_interior]