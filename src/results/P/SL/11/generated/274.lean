

theorem interior_prod_closure_eq_prod_interiors
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) :
    interior (closure (A : Set X) ×ˢ closure (B : Set Y)) =
      interior (closure A) ×ˢ interior (closure B) := by
  simpa [interior_prod_eq]