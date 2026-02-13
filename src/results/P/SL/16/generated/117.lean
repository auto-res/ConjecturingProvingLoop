

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  -- First, use monotonicity of `closure`.
  have h₁ : closure A ⊆ closure B := closure_mono hAB
  -- Next, apply monotonicity of `interior`.
  have h₂ : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h₁
  -- Finally, apply `closure` once more.
  exact closure_mono h₂