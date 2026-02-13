

theorem interior_closure_prod_eq_prod_interiors {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) :
    interior (closure (A ×ˢ B)) = interior (closure A) ×ˢ interior (closure B) := by
  simpa [interior_prod_eq] using
    (interior_closure_prod_eq (A := A) (B := B))