

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact subset_trans hP2 interior_subset

theorem P1_of_isOpen {A : Set X} (hA : IsOpen A) : P1 A := by
  dsimp [P1]
  simpa [hA.interior_eq] using subset_closure

theorem P2_of_isOpen {A : Set X} (hA : IsOpen A) : P2 A := by
  dsimp [P2]
  have h : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  simpa [hA.interior_eq] using h

theorem P3_of_isClosed {A : Set X} (hA : IsClosed A) : P3 (interior A) := by
  dsimp [P3]
  simpa [interior_interior] using
    (interior_mono (s := interior A) (t := closure (interior A)) subset_closure)

theorem P2_union {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  dsimp [P2] at *
  -- Upgrade the inclusions supplied by `hA` and `hB`
  have hA' : (A : Set X) ⊆ interior (closure (interior (A ∪ B))) := by
    refine Set.Subset.trans hA ?_
    -- `interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B)))`
    have : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
      have : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact closure_mono this
    exact interior_mono this
  have hB' : (B : Set X) ⊆ interior (closure (interior (A ∪ B))) := by
    refine Set.Subset.trans hB ?_
    -- `interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B)))`
    have : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
      have : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact closure_mono this
    exact interior_mono this
  -- Combine the two inclusions to obtain the desired result
  exact Set.union_subset hA' hB'

theorem P1_sUnion {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P1 A) : P1 (⋃₀ 𝒜) := by
  dsimp [P1]
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hA_P1 : (A : Set X) ⊆ closure (interior A) := h A hA_mem
  have hx_closureA : x ∈ closure (interior A) := hA_P1 hxA
  have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have h_inter : interior A ⊆ interior (⋃₀ 𝒜) := interior_mono h_sub
  have h_subset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_inter
  exact h_subset hx_closureA