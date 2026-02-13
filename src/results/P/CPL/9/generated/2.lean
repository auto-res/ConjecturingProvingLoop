

theorem P3_Union {ι} (s : ι → Set X) (h : ∀ i, P3 (s i)) : P3 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
  have hx_int : x ∈ interior (closure (s i)) := h i hi
  have h_subset : interior (closure (s i)) ⊆ interior (closure (⋃ j, s j)) := by
    apply interior_mono
    have h_closure : closure (s i) ⊆ closure (⋃ j, s j) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact h_closure
  exact h_subset hx_int

theorem P2_of_open {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have hx_cl : x ∈ interior (closure A) :=
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx_int
  simpa [hA.interior_eq] using hx_cl

theorem P3_of_open {A : Set X} (hA : IsOpen A) : P3 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have h_sub : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact h_sub hx_int

theorem P2_sUnion {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P2 A) : P2 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hx_int : x ∈ interior (closure (interior A)) := (h A hA_mem) hxA
  have hA_subset : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) :=
    interior_mono hA_subset
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_int_subset
  have h_final :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) :=
    interior_mono h_closure_subset
  exact h_final hx_int