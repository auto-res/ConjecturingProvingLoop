

theorem denseInterior_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P2 (closure A) := by
  intro hDense
  dsimp [Topology.P2]
  intro x _hx
  -- `closure (interior A)` is the whole space
  have h_closure_intA : closure (interior A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- `interior A ⊆ interior (closure A)`
  have h_int_subset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- hence `closure (interior A) ⊆ closure (interior (closure A))`
  have h_closure_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (closure A)) :=
    closure_mono h_int_subset
  -- Using the previous equality, this forces `closure (interior (closure A)) = univ`
  have h_closure_eq_univ :
      closure (interior (closure A)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _; exact Set.mem_univ y
    · have : (Set.univ : Set X) ⊆ closure (interior (closure A)) := by
        simpa [h_closure_intA] using h_closure_subset
      exact this
  -- Therefore its interior is also `univ`.
  have h_interior_univ :
      interior (closure (interior (closure A))) = (Set.univ : Set X) := by
    simpa [h_closure_eq_univ, interior_univ]
  -- Conclude the desired membership.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_interior_univ] using this