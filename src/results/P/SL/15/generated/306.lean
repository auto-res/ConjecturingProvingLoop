

theorem interior_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} :
    interior (A ×ˢ (Set.univ : Set Y)) = interior A ×ˢ (Set.univ : Set Y) := by
  simpa [interior_univ] using
    (interior_prod_eq (s := A) (t := (Set.univ : Set Y)))