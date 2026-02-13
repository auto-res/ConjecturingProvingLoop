

theorem P3_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : interior A = Set.univ) : P3 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA] using (by triv)
  have h_sub : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact h_sub hx_int

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  simpa [P2, P3, hA.interior_eq]

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι} (s : ι → Set X) (h : ∀ i, P2 (s i)) : P2 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
  have hx_int : x ∈ interior (closure (interior (s i))) := (h i) hi
  have h_subset :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) := by
    apply interior_mono
    have h_closure :
        closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) := by
      apply closure_mono
      have h_int :
          interior (s i) ⊆ interior (⋃ j, s j) := by
        apply interior_mono
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact h_int
    exact h_closure
  exact h_subset hx_int

theorem P2_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → A ⊆ closure (interior A) := by
  intro hP2
  exact (P2_imp_P1 (A := A)) hP2