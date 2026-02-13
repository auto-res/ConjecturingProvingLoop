

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure (A : Set X) = closure (interior A) := by
  dsimp [Topology.P1]
  constructor
  · intro hP1
    have h₁ : closure A ⊆ closure (interior A) := by
      simpa using (closure_mono hP1)
    have h₂ : closure (interior A) ⊆ closure A := by
      exact closure_mono (interior_subset : interior A ⊆ A)
    exact subset_antisymm h₁ h₂
  · intro hEq
    have hA : (A : Set X) ⊆ closure A := subset_closure
    simpa [hEq] using hA