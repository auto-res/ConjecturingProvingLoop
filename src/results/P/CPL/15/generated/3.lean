

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  intro x hx
  exact mem_interior.mpr ⟨interior A, subset_closure, isOpen_interior, hx⟩

theorem P3_exists_subset_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U ⊆ closure A := by
  refine ⟨interior (closure A), isOpen_interior, hA, ?_⟩
  have h_subset :
      (closure (interior (closure A)) : Set X) ⊆ closure (closure A) :=
    closure_mono (interior_subset : interior (closure A) ⊆ closure A)
  simpa [closure_closure] using h_subset

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} (h : ∀ A, A ∈ ℬ → P1 A) : P1 (⋃₀ ℬ) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hAx⟩
  have hPA : P1 A := h A hA_mem
  have hx_cl : x ∈ closure (interior A) := hPA hAx
  have h_subset : (closure (interior A) : Set X) ⊆ closure (interior (⋃₀ ℬ)) := by
    exact closure_mono (interior_mono (Set.subset_sUnion_of_mem hA_mem))
  exact h_subset hx_cl