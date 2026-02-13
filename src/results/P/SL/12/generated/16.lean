

theorem Topology.closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.P1 (X := X) A) :
    closure (A : Set X) = closure (interior A) := by
  -- `closure (interior A)` is always a subset of `closure A`
  have h₁ : closure (interior A) ⊆ closure (A : Set X) :=
    closure_mono interior_subset
  -- From `P1` we have `A ⊆ closure (interior A)`
  have hA' : (A : Set X) ⊆ closure (interior A) := hA
  -- Taking closures gives the reverse inclusion
  have h₂ : closure (A : Set X) ⊆ closure (interior A) := by
    have : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hA'
    simpa [closure_closure] using this
  exact Set.Subset.antisymm h₂ h₁