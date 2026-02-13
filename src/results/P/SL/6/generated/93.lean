

theorem interior_closure_eq_self_of_P3_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    interior (closure (A : Set X)) = A := by
  -- First, `interior (closure A) ⊆ A` because `A` is closed.
  have h₁ : interior (closure (A : Set X)) ⊆ A := by
    have h : interior (closure (A : Set X)) ⊆ closure (A : Set X) :=
      interior_subset
    simpa [hA_closed.closure_eq] using h
  -- Second, `A ⊆ interior (closure A)` by `P3`.
  have h₂ : (A : Set X) ⊆ interior (closure A) := by
    dsimp [Topology.P3] at hP3
    exact hP3
  exact subset_antisymm h₁ h₂