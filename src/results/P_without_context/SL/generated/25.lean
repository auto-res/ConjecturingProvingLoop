

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hA
  have hIncl : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono hcl
  exact Set.Subset.trans hA hIncl