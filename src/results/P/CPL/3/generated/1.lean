

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} : (∀ A ∈ ℬ, P3 A) → P3 (⋃₀ ℬ) := by
  intro hP3 x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℬ, hxA⟩
  have hx_in : x ∈ interior (closure A) := (hP3 A hAℬ) hxA
  have h_subset : interior (closure A) ⊆ interior (closure (⋃₀ ℬ)) := by
    apply interior_mono
    apply closure_mono
    exact Set.subset_sUnion_of_mem hAℬ
  exact h_subset hx_in

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  have hfalse : False := by
    simpa [Set.mem_empty_iff_false] using hx
  exact hfalse.elim

theorem P2_self {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  simpa [interior_interior] using (hsubset hx)

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, P3 (s i)) → P3 (⋃ i, s i) := by
  intro hP3 x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_in : x ∈ interior (closure (s i)) := (hP3 i) hx_i
  have h_subset :
      interior (closure (s i)) ⊆
        interior (closure (⋃ j, s j)) := by
    apply interior_mono
    apply closure_mono
    exact Set.subset_iUnion _ i
  exact h_subset hx_in