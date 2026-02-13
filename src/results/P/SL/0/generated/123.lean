

theorem closure_interior_closure_eq_closure_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A →
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  intro hP3
  -- `closure A` is contained in `closure (interior (closure A))` by `P3`.
  have h₁ : closure (A : Set X) ⊆
      closure (interior (closure (A : Set X))) := by
    have hSub : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
    exact closure_mono hSub
  -- The reverse inclusion holds by monotonicity of `closure`.
  have h₂ :
      closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) :=
    Topology.closure_interior_closure_subset_closure (X := X) (A := A)
  exact subset_antisymm h₂ h₁