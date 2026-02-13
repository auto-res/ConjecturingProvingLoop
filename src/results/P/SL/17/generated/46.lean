

theorem Topology.closure_interior_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  ·
    -- `LHS ⊆ RHS`
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆ closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  ·
    -- `RHS ⊆ LHS`
    have h₁ : interior A ⊆ interior (closure (interior A)) := by
      have h_sub : interior A ⊆ closure (interior A) := subset_closure
      exact interior_maximal h_sub isOpen_interior
    have h₂ : closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    exact h₂