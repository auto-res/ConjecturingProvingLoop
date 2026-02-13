

theorem Topology.dense_interior_implies_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → closure (interior A) = closure A := by
  intro hDense
  -- `closure (interior A)` is the whole space.
  have hUniv : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- One inclusion is monotonicity of `closure`.
  have h₁ :
      (closure (interior (A : Set X)) : Set X) ⊆ closure A :=
    closure_mono (interior_subset : (interior (A : Set X) : Set X) ⊆ A)
  -- The other inclusion is trivial after rewriting with `hUniv`.
  have h₂ :
      (closure (A : Set X)) ⊆ closure (interior (A : Set X)) := by
    intro x hx
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [hUniv] using this
  exact Set.Subset.antisymm h₁ h₂