

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A :=
by
  intro h
  unfold P2 P1 at *
  exact Set.Subset.trans h (by
    simpa using (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)))