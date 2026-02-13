

theorem closure_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (B : Set Y) :
    closure ((Set.univ : Set X) ×ˢ B) = (Set.univ : Set X) ×ˢ closure B := by
  simpa [closure_univ] using
    (closure_prod_eq (s := (Set.univ : Set X)) (t := B))