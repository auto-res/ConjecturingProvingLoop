

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} : (∀ A ∈ ℬ, P2 A) → P2 (⋃₀ ℬ) := by
  intro hP2
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℬ, hxA⟩
  have hx_in : x ∈ interior (closure (interior A)) := (hP2 A hAℬ) hxA
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ ℬ))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    exact Set.subset_sUnion_of_mem hAℬ
  exact h_subset hx_in

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 A := by
  intro h_dense x hx
  simpa [h_dense, interior_univ] using (Set.mem_univ x)