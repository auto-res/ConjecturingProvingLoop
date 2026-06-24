

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro hA
  unfold P2 P1 at *
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact subset_trans hA hsubset