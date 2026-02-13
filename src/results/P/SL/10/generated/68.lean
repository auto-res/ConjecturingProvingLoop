

theorem Topology.closure_eq_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure A = closure (interior (closure A)) := by
  intro hP3
  apply Set.Subset.antisymm
  ·
    -- Show `closure A ⊆ closure (interior (closure A))`.
    have h₁ : A ⊆ closure (interior (closure A)) := by
      intro x hxA
      have hx_int : x ∈ interior (closure A) := hP3 hxA
      exact subset_closure hx_int
    exact closure_minimal h₁ isClosed_closure
  ·
    -- The reverse inclusion follows from monotonicity.
    have h₂ : interior (closure A) ⊆ closure A := interior_subset
    have h₃ : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono h₂
    simpa [closure_closure] using h₃