

theorem closure_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) :
    closure (A ×ˢ (Set.univ : Set Y)) = (closure A) ×ˢ (Set.univ : Set Y) := by
  simpa [closure_univ] using
    (closure_prod_eq (s := A) (t := (Set.univ : Set Y)))