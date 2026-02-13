

theorem interior_prod_of_isOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ×ˢ B) = A ×ˢ B := by
  have h := interior_prod_eq (s := A) (t := B)
  simpa [hA.interior_eq, hB.interior_eq] using h