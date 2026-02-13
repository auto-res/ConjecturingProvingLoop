

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  have hfalse : False := by
    simpa [Set.mem_empty_iff_false] using hx
  exact hfalse.elim

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  intro x hx
  have hsubset : (interior A) ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  exact hsubset hx

theorem P2_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2 x hx
  exact interior_subset (hP2 hx)

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} : (∀ A ∈ ℬ, P1 A) → P1 (⋃₀ ℬ) := by
  intro h
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℬ, hxA⟩
  have hx_closure : x ∈ closure (interior A) := (h A hAℬ) hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ ℬ)) := by
    apply closure_mono
    apply interior_mono
    exact Set.subset_sUnion_of_mem hAℬ
  exact hsubset hx_closure

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, P2 (s i)) → P2 (⋃ i, s i) := by
  intro hP2
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_in : x ∈ interior (closure (interior (s i))) := (hP2 i) hx_i
  have h_subset :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    exact Set.subset_iUnion _ i
  exact h_subset hx_in