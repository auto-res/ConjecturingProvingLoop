

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hP2
  have h : A ⊆ closure (interior A) :=
    (Set.Subset.trans (by
        simpa [P2] using hP2) interior_subset)
  simpa [P1] using h