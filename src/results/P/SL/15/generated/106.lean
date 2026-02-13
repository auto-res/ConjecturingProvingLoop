

theorem denseInterior_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 A := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  -- `closure (interior A)` is the whole space
  have h_closure_int : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- hence its interior is also the whole space
  have h_int_eq : interior (closure (interior A)) = (Set.univ : Set X) := by
    have : interior (closure (interior A)) = interior ((Set.univ : Set X)) := by
      simpa [h_closure_int] using rfl
    simpa [interior_univ] using this
  -- `interior (closure (interior A)) ⊆ interior (closure A)`
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure_mono : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono h_closure_mono
  -- Therefore, `interior (closure A)` is the whole space
  have h_univ_subset : (Set.univ : Set X) ⊆ interior (closure A) := by
    simpa [h_int_eq] using h_subset
  -- Conclude the desired membership
  have hx_in : x ∈ interior (closure A) := h_univ_subset (by trivial)
  exact hx_in