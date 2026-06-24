

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A : Set X) → P1 A := by
  intro hP2
  have hsubset :
      interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using
      (interior_subset :
        interior (closure (interior A)) ⊆ closure (interior A))
  exact Set.Subset.trans hP2 hsubset