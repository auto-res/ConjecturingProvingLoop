

theorem P2_imp_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → (P1 A ∧ P3 A) :=
by
  intro hP2
  -- Derive P1 from P2
  have hP1 : P1 A := by
    have : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
    exact Set.Subset.trans hP2 this
  -- Derive P3 from P2
  have hP3 : P3 A := by
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    have h₂ : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono h₁
    exact Set.Subset.trans hP2 h₂
  exact And.intro hP1 hP3