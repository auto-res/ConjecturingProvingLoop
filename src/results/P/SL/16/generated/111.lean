

theorem Topology.closure_eq_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (X := X) A) :
    closure A = closure (interior (closure A)) := by
  apply subset_antisymm
  · -- `closure A ⊆ closure (interior (closure A))` via monotonicity of `closure`
    have h : A ⊆ interior (closure A) := hP3
    exact closure_mono h
  · -- `closure (interior (closure A)) ⊆ closure A`
    have h₁ : interior (closure A) ⊆ closure A := interior_subset
    have h₂ : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono h₁
    simpa [closure_closure] using h₂