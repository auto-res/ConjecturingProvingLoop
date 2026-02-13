

theorem denseInterior_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P1 (closure A) := by
  intro hDense
  dsimp [Topology.P1]
  intro x hx
  -- `closure (interior A)` is the whole space
  have h_closure_eq : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- hence `x` belongs to `closure (interior A)`
  have hx_intA : x ∈ closure (interior A) := by
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [h_closure_eq] using this
  -- `interior A` is contained in `interior (closure A)`
  have h_int_subset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- taking closures preserves inclusion
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_intA