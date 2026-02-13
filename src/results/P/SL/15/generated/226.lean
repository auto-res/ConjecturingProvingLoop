

theorem interior_closure_interior_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    interior (closure (interior (A ×ˢ B))) =
      interior (closure (interior A)) ×ˢ
        interior (closure (interior B)) := by
  -- First, rewrite the closure of the interior of the product.
  have h₁ :
      closure (interior (A ×ˢ B)) =
        closure (interior A) ×ˢ closure (interior B) := by
    simpa using
      (closure_interior_prod (X := X) (Y := Y) (A := A) (B := B))
  -- Next, identify the interior of a product of sets.
  have h₂ :
      interior ((closure (interior A)) ×ˢ (closure (interior B))) =
        interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) := by
    simpa using
      (interior_prod_eq
        (s := closure (interior A)) (t := closure (interior B)))
  -- Combine the two equalities.
  simpa [h₁, h₂]