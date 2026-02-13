

theorem interior_closure_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    interior (closure (A ×ˢ B)) = interior (closure A) ×ˢ interior (closure B) := by
  have h₁ : closure (A ×ˢ B) = closure A ×ˢ closure B := by
    simpa using closure_prod_eq (s := A) (t := B)
  have h₂ :
      interior ((closure A) ×ˢ (closure B)) =
        interior (closure A) ×ˢ interior (closure B) := by
    simpa using interior_prod_eq (s := closure A) (t := closure B)
  simpa [h₁, h₂]