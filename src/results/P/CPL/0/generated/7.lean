

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} : (∀ B ∈ 𝒮, P2 B) → P2 (⋃₀ 𝒮) := by
  intro h𝒮
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨B, hBmem, hxB⟩
  have hP2B : P2 (B : Set X) := h𝒮 B hBmem
  have hx_intB : x ∈ interior (closure (interior (B : Set X))) := hP2B hxB
  have h_subset :
      interior (closure (interior (B : Set X)))
        ⊆ interior (closure (interior (⋃₀ 𝒮))) := by
    have h_int_sub : interior (B : Set X) ⊆ interior (⋃₀ 𝒮) := by
      have h_sub : (B : Set X) ⊆ ⋃₀ 𝒮 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨B, hBmem, hy⟩
      exact interior_mono h_sub
    have h_cl_sub :
        closure (interior (B : Set X))
          ⊆ closure (interior (⋃₀ 𝒮)) :=
      closure_mono h_int_sub
    exact interior_mono h_cl_sub
  exact h_subset hx_intB

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} : (∀ B ∈ 𝒮, P3 B) → P3 (⋃₀ 𝒮) := by
  intro h𝒮
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨B, hBmem, hxB⟩
  have hP3B : P3 (B : Set X) := h𝒮 B hBmem
  have hx_intClB : x ∈ interior (closure (B : Set X)) := hP3B hxB
  have h_subset :
      interior (closure (B : Set X)) ⊆ interior (closure (⋃₀ 𝒮)) := by
    have h_closure : closure (B : Set X) ⊆ closure (⋃₀ 𝒮) := by
      have h_sub : (B : Set X) ⊆ ⋃₀ 𝒮 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨B, hBmem, hy⟩
      exact closure_mono h_sub
    exact interior_mono h_closure
  exact h_subset hx_intClB

theorem exists_closed_superset_P1 {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ C, A ⊆ C ∧ IsClosed C ∧ P1 C := by
  refine ⟨Set.univ, ?_, isClosed_univ, ?_⟩
  · exact Set.subset_univ A
  · intro x hx
    simpa [interior_univ, closure_univ] using hx