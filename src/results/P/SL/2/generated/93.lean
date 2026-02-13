

theorem Topology.closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  ·
    have h₁ :
        (interior (closure (interior A)) : Set X) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  ·
    have h₁ :
        (interior A : Set X) ⊆ interior (closure (interior A)) := by
      have hSub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
      exact interior_maximal hSub isOpen_interior
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    exact h₂