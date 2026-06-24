

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hP2
  exact fun x hxA =>
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
      (hP2 hxA)