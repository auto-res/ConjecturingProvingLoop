

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A : Set X) → P1 A := by
  intro hA
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact Set.Subset.trans hA h₁