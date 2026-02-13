

theorem interior_closure_prod_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) :
    interior (closure (A ×ˢ B)) = interior (closure A ×ˢ closure B) := by
  simpa [closure_prod_eq]