

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  -- First, use the monotonicity of `interior ∘ closure` under the assumption `A ⊆ B`.
  have h₁ : interior (closure A) ⊆ interior (closure B) :=
    Topology.interior_closure_mono (A := A) (B := B) hAB
  -- Taking closures preserves inclusions.
  exact closure_mono h₁