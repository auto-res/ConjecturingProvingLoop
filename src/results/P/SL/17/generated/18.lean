

theorem Topology.closure_interior_eq_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    closure (interior A) = closure A := by
  apply subset_antisymm
  ·
    exact closure_mono (interior_subset : interior A ⊆ A)
  ·
    have h₁ : A ⊆ closure (interior A) := hP1
    have h₂ : closure A ⊆ closure (closure (interior A)) := closure_mono h₁
    simpa [closure_closure] using h₂