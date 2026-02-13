

theorem Topology.closure_interior_eq_of_subset_of_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hB : B ⊆ closure (interior A)) :
    closure (interior A) = closure (interior B) := by
  -- We will prove the two inclusions separately and then invoke `subset_antisymm`.
  apply subset_antisymm
  ·
    -- From `A ⊆ B` we get `interior A ⊆ interior B`,
    -- and taking closures preserves inclusions.
    exact closure_mono (interior_mono hAB)
  ·
    -- From `B ⊆ closure (interior A)` we obtain
    -- `interior B ⊆ interior (closure (interior A))`.
    have h₁ : interior B ⊆ interior (closure (interior A)) :=
      interior_mono hB
    -- Taking closures preserves inclusions.
    have h₂ : closure (interior B) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    -- Simplify the right‐hand side using idempotence of `closure ∘ interior`.
    simpa [Topology.closure_interior_idempotent (A := A)] using h₂