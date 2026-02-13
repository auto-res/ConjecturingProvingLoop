

theorem interior_closure_prod_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    interior (closure A) ×ˢ interior (closure B) ⊆
      interior (closure (A ×ˢ B)) := by
  intro z hz
  have hEq :
      interior (closure (A ×ˢ B)) =
        interior (closure A) ×ˢ interior (closure B) :=
    interior_closure_prod (X := X) (Y := Y) (A := A) (B := B)
  simpa [hEq] using hz