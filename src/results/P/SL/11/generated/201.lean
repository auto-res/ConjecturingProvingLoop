

theorem closure_interior_prod_eq_prod_closure_interiors
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) :
    closure ((interior A) ×ˢ (interior B)) =
      closure (interior A) ×ˢ closure (interior B) := by
  simpa using
    (closure_prod_eq :
      closure ((interior A) ×ˢ (interior B)) =
        closure (interior A) ×ˢ closure (interior B))