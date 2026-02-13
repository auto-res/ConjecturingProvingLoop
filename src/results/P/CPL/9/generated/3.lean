

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P1 A) : P1 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hx_cl : x ∈ closure (interior A) := (h A hA_mem) hxA
  have hA_subset : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) :=
    interior_mono hA_subset
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_cl