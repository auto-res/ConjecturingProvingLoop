

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hA
  exact
    Set.Subset.trans hA
      (by
        simpa using
          (interior_subset :
            interior (closure (interior A)) ⊆ closure (interior A)))