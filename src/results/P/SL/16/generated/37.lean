

theorem Topology.closure_interior_eq_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A) :
    closure (interior A) = closure A := by
  apply subset_antisymm
  · -- `closure (interior A) ⊆ closure A` by monotonicity of `closure`
    exact closure_mono (interior_subset : interior A ⊆ A)
  · -- For the reverse inclusion use `A ⊆ closure (interior A)` from `P1`
    have h : A ⊆ closure (interior A) := hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono h
    simpa [closure_closure] using this