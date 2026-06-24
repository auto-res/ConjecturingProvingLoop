

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  exact h.trans (by
    simpa using
      (interior_subset :
        interior (closure (interior A)) ⊆ closure (interior A)))