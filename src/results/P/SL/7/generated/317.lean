

theorem Topology.interiorClosure_inter_interSubset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆ interior (closure A) := by
  -- We start with the basic inclusion `A ∩ interior B ⊆ A`.
  have h₀ : (A ∩ interior B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions, giving
  -- `closure (A ∩ interior B) ⊆ closure A`.
  have h₁ : closure (A ∩ interior B) ⊆ closure A :=
    closure_mono h₀
  -- Finally, apply monotonicity of `interior`.
  exact interior_mono h₁