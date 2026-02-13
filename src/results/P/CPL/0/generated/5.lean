

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hP2 hx
  have h_subset :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono
      (closure_mono (interior_subset : (interior A : Set X) ⊆ A))
  exact h_subset hx'

theorem P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 (closure A) := by
  intro hP2
  -- Obtain `A ⊆ interior (closure A)` from `P2 A`
  have hSub : (A : Set X) ⊆ interior (closure A) := by
    have hP3 : P3 A := P2_imp_P3 hP2
    simpa using hP3
  -- Conclude `closure A ⊆ closure (interior (closure A))`
  exact fun x hx => (closure_mono hSub) hx

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  exact P3_of_open isOpen_interior

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} : (∀ B, B ∈ 𝒮 → P1 B) → P1 (⋃₀ 𝒮) := by
  intro h𝒮
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨B, hBmem, hxB⟩
  have hP1B : P1 (B : Set X) := h𝒮 B hBmem
  have hx_clB : x ∈ closure (interior (B : Set X)) := hP1B hxB
  have h_subset : closure (interior (B : Set X)) ⊆ closure (interior (⋃₀ 𝒮)) := by
    have h_int_subset : interior (B : Set X) ⊆ interior (⋃₀ 𝒮) := by
      have h_subset_set : (B : Set X) ⊆ ⋃₀ 𝒮 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨B, hBmem, hy⟩
      exact interior_mono h_subset_set
    exact closure_mono h_int_subset
  exact h_subset hx_clB