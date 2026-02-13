

theorem Topology.closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    -- First, show `closure (interior (closure (interior A))) ⊆ closure (interior A)`.
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  ·
    -- Now, show `closure (interior A) ⊆ closure (interior (closure (interior A)))`.
    have h₁ : interior A ⊆ interior (closure (interior A)) := by
      have h : interior A ⊆ closure (interior A) := subset_closure
      have : interior (interior A) ⊆ interior (closure (interior A)) :=
        interior_mono h
      simpa [interior_interior] using this
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    exact h₂