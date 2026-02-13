

theorem interior_prod_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    interior A ×ˢ interior B ⊆ interior (A ×ˢ B) := by
  -- We rely on the characterization of the interior of a product.
  have h : interior (A ×ˢ B) = interior A ×ˢ interior B := by
    simpa using interior_prod_eq (s := A) (t := B)
  intro z hz
  -- Transport the membership through the equality `h`.
  simpa [h] using hz