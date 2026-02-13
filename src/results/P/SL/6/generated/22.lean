

theorem P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) ↔ closure (interior A) = closure A := by
  constructor
  · intro hA
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    have h₂ : closure A ⊆ closure (interior A) := by
      have h := closure_mono hA
      simpa [closure_closure] using h
    exact subset_antisymm h₁ h₂
  · intro hEq
    dsimp [Topology.P1]
    have h : (A : Set X) ⊆ closure A := subset_closure
    simpa [hEq] using h