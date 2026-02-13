

theorem P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ∧ P3 A → P2 A := by
  rintro ⟨hP1, hP3⟩
  intro x hx
  -- `x ∈ interior (closure A)` by `P3`
  have hx_int_closureA : x ∈ interior (closure A) := hP3 hx
  -- `closure A ⊆ closure (interior A)` thanks to `P1`
  have h_closure_subset : closure A ⊆ closure (interior A) := by
    simpa [closure_closure] using (closure_mono hP1)
  -- taking interiors preserves the inclusion
  have h_subset :
      interior (closure A) ⊆ interior (closure (interior A)) :=
    interior_mono h_closure_subset
  exact h_subset hx_int_closureA

theorem exists_open_neighborhood_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A := by
  intro x hx
  have hx_int : x ∈ interior (closure A) := hA hx
  refine ⟨interior (closure A), isOpen_interior, hx_int, ?_⟩
  exact interior_subset