

theorem Topology.closureInterior_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure (interior A) = closure A := by
  intro hP1
  -- `closure (interior A)` is always contained in `closure A`
  have h₁ : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- From `P1`, `A ⊆ closure (interior A)`, hence `closure A ⊆ closure (interior A)`
  have h₂ : closure A ⊆ closure (interior A) := by
    have h : closure A ⊆ closure (closure (interior A)) :=
      closure_mono (hP1 : (A : Set X) ⊆ closure (interior A))
    simpa [closure_closure] using h
  exact Set.Subset.antisymm h₁ h₂