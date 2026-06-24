

theorem P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro h
  simpa [P1, P2] using (Set.Subset.trans h interior_subset)