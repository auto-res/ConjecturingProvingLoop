

theorem closure_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : closure A = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    have h₁ : (closure A : Set X) ⊆ closure (closure (interior A)) := closure_mono h
    simpa [closure_closure] using h₁
  ·
    exact closure_mono (interior_subset : interior A ⊆ A)

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} (h : ∀ A, A ∈ ℬ → P2 A) : P2 (⋃₀ ℬ) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hAx⟩
  have hPA : P2 A := h A hA_mem
  have hxA : x ∈ interior (closure (interior A)) := hPA hAx
  have h_subset :
      (interior (closure (interior A)) : Set X) ⊆
        interior (closure (interior (⋃₀ ℬ))) :=
    interior_mono
      (closure_mono
        (interior_mono
          (Set.subset_sUnion_of_mem hA_mem)))
  exact h_subset hxA

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} (h : ∀ A, A ∈ ℬ → P3 A) : P3 (⋃₀ ℬ) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hPA : P3 A := h A hA_mem
  have hx_int : x ∈ interior (closure A) := hPA hxA
  have h_subset :
      interior (closure A) ⊆ interior (closure (⋃₀ ℬ)) :=
    interior_mono
      (closure_mono
        (Set.subset_sUnion_of_mem hA_mem))
  exact h_subset hx_int

theorem P3_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : P3 A) : closure A = closure (interior (closure A)) := by
  apply Set.Subset.antisymm
  ·
    exact closure_mono (h : (A : Set X) ⊆ interior (closure A))
  ·
    have : (closure (interior (closure A)) : Set X) ⊆ closure A :=
      calc
        closure (interior (closure A)) ⊆ closure (closure A) :=
          closure_mono (interior_subset : interior (closure A) ⊆ closure A)
        _ = closure A := by simpa [closure_closure]
    exact this