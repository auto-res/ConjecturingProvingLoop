

theorem denseInterior_prod_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hAne : (interior A).Nonempty) (hBne : (interior B).Nonempty) :
    Dense (interior (A ×ˢ B)) ↔
      (Dense (interior A) ∧ Dense (interior B)) := by
  -- Identify the interior of a product.
  have hInt : interior (A ×ˢ B) = (interior A) ×ˢ (interior B) := by
    simpa using interior_prod_eq (s := A) (t := B)
  -- Rewrite the goal with this identification.
  have hRew :
      Dense (interior (A ×ˢ B)) ↔
        Dense ((interior A) ×ˢ (interior B)) := by
    simpa [hInt]
  -- Apply the density criterion for products to the interiors.
  have hProd :=
    (dense_prod_iff
        (X := X) (Y := Y)
        (A := interior A) (B := interior B)
        (hAne := hAne) (hBne := hBne))
  -- Combine the two equivalences.
  exact hRew.trans hProd