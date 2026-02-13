

theorem Topology.closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h₁ :
        (interior (closure (interior A)) : Set X) ⊆ closure (interior A) := by
      intro x hx
      exact (interior_subset : interior (closure (interior A)) ⊆
        closure (interior A)) hx
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) := closure_mono h₁
    simpa [closure_closure] using h₂
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h₁ :
        (interior A : Set X) ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (A := A)
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    simpa using h₂