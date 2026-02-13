

theorem P2_bUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {s : Set ι} (f : ι → Set X) (h : ∀ i ∈ s, P2 (f i)) : P2 (⋃ i ∈ s, f i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx_i⟩
  rcases Set.mem_iUnion.mp hx_i with ⟨hi_mem_s, hx_fi⟩
  have hP2i : P2 (f i) := h i hi_mem_s
  have hx_int : x ∈ interior (closure (interior (f i))) := hP2i hx_fi
  have hsubset :
      interior (closure (interior (f i))) ⊆
        interior (closure (interior (⋃ i ∈ s, f i))) := by
    -- Start with the basic inclusion `f i ⊆ ⋃ i ∈ s, f i`.
    have hsub : (f i : Set X) ⊆ ⋃ i ∈ s, f i := by
      intro y hy
      -- Inner union over the proof `i ∈ s`.
      have hinner : y ∈ ⋃ (hi : i ∈ s), f i := by
        refine Set.mem_iUnion.mpr ?_
        exact ⟨hi_mem_s, hy⟩
      -- Outer union over the index `i`.
      refine Set.mem_iUnion.mpr ?_
      exact ⟨i, hinner⟩
    -- Now propagate the inclusion through `interior`, `closure`, `interior`.
    have hsub_int : interior (f i) ⊆ interior (⋃ i ∈ s, f i) :=
      interior_mono hsub
    have hsub_cl : closure (interior (f i)) ⊆
        closure (interior (⋃ i ∈ s, f i)) :=
      closure_mono hsub_int
    exact interior_mono hsub_cl
  exact hsubset hx_int

theorem P3_bUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {s : Set ι} (f : ι → Set X) (h : ∀ i ∈ s, P3 (f i)) : P3 (⋃ i ∈ s, f i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx_i⟩
  rcases Set.mem_iUnion.mp hx_i with ⟨hi_mem_s, hx_fi⟩
  have hP3i : P3 (f i) := h i hi_mem_s
  have hx_int : x ∈ interior (closure (f i)) := hP3i hx_fi
  have hsubset :
      interior (closure (f i)) ⊆
        interior (closure (⋃ i ∈ s, f i)) := by
    -- First, show `f i ⊆ ⋃ i ∈ s, f i`.
    have hsub : (f i : Set X) ⊆ ⋃ i ∈ s, f i := by
      intro y hy
      -- Membership in the inner union over proofs `i ∈ s`.
      have hinner : y ∈ ⋃ (hi : i ∈ s), f i := by
        refine Set.mem_iUnion.mpr ?_
        exact ⟨hi_mem_s, hy⟩
      -- Membership in the outer union over indices `i`.
      refine Set.mem_iUnion.mpr ?_
      exact ⟨i, hinner⟩
    -- Propagate the inclusion through `closure` and `interior`.
    have hsub_cl : closure (f i) ⊆ closure (⋃ i ∈ s, f i) :=
      closure_mono hsub
    exact interior_mono hsub_cl
  exact hsubset hx_int