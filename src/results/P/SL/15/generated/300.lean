

theorem closure_prod_closure_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    closure ((closure A) ×ˢ (closure B) : Set (X × Y)) =
      (closure A) ×ˢ (closure B) := by
  calc
    closure ((closure A) ×ˢ (closure B) : Set (X × Y))
        = closure (closure A) ×ˢ closure (closure B) := by
          simpa using
            (closure_prod_eq (s := closure A) (t := closure B))
    _ = (closure A) ×ˢ (closure B) := by
          simpa [closure_closure]