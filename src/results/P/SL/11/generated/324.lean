

theorem closure_interior_prod_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) :
    closure (interior (A ×ˢ B)) = closure ((interior A) ×ˢ (interior B)) := by
  simpa [interior_prod_eq]