

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (X := X) A → P1 (X := X) A :=
by
  intro h
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact subset_trans h h₁