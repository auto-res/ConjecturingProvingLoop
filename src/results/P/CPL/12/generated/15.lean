

theorem P1_of_sUnion_eq_univ {X : Type*} [TopologicalSpace X] {ℱ : Set (Set X)} : (⋃₀ ℱ) = Set.univ → P1 (⋃₀ ℱ) := by
  intro hEq
  simpa [hEq] using (P1_univ : P1 (Set.univ : Set X))