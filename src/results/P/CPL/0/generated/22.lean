

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, P3 (s i)) → P3 (⋃ i, s i) := by
  intro hP3
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hP3i : P3 (s i) := hP3 i
  have hx_int : x ∈ interior (closure (s i : Set X)) := hP3i hx_i
  have h_subset :
      interior (closure (s i : Set X))
        ⊆ interior (closure (⋃ j, s j)) := by
    have h_closure :
        closure (s i : Set X) ⊆ closure (⋃ j, s j) := by
      have h_sub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_sub
    exact interior_mono h_closure
  exact h_subset hx_int