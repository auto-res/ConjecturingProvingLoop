

theorem closure_interior_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    closure (interior (A ×ˢ B)) = closure (interior A) ×ˢ closure (interior B) := by
  have h : interior (A ×ˢ B) = interior A ×ˢ interior B := by
    simpa using interior_prod_eq (s := A) (t := B)
  calc
    closure (interior (A ×ˢ B))
        = closure (interior A ×ˢ interior B) := by
          simpa [h]
    _ = closure (interior A) ×ˢ closure (interior B) := by
          simpa using closure_prod_eq (s := interior A) (t := interior B)