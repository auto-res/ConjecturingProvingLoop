

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hAx =>
      have hx_int_clA : x ∈ interior (closure A) := hA hAx
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_left
      exact hsubset hx_int_clA
  | inr hBx =>
      have hx_int_clB : x ∈ interior (closure B) := hB hBx
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_right
      exact hsubset hx_int_clB

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P2 A) → P2 (⋃₀ 𝒜) := by
  intro hP2
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : P2 A := hP2 A hA_mem
  have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    -- First, relate `interior A` to `interior (⋃₀ 𝒜)`.
    have h1 : interior A ⊆ interior (⋃₀ 𝒜) :=
      interior_mono (Set.subset_sUnion_of_mem hA_mem)
    -- Then, take closures of both sides.
    have h2 : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono h1
    -- Finally, take interiors again.
    exact interior_mono h2
  exact h_subset hx_in

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P1 A) → P1 (⋃₀ 𝒜) := by
  intro hP1
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A : P1 A := hP1 A hA_mem
  have hx_closure : x ∈ closure (interior A) := hP1A hxA
  have h_subset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    apply closure_mono
    apply interior_mono
    exact Set.subset_sUnion_of_mem hA_mem
  exact h_subset hx_closure

theorem P2_to_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  intro x hx
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hx
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    exact interior_mono h_closure
  exact h_subset hx_int

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 A := by
  intro hDense x hx
  simpa [hDense, interior_univ] using (Set.mem_univ x)