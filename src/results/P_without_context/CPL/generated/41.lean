

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  dsimp [P1]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  dsimp [P2]
  intro x hx
  -- First, view `hx` as a membership in `interior (interior A)`.
  have hx' : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx
  -- `interior A` is contained in its closure, hence their interiors satisfy the same.
  have hsubset :
      interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono
      (subset_closure : (interior A) ⊆ closure (interior A))
  -- Apply the inclusion to obtain the goal.
  have : x ∈ interior (closure (interior A)) := hsubset hx'
  simpa [interior_interior] using this

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P3 A := by
  dsimp [P2] at h
  dsimp [P3]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have hclosure : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hclosure
  exact hsubset hx'

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  -- Expand the hypotheses `hA` and `hB`
  dsimp [P1] at hA hB
  -- Unfold the goal
  dsimp [P1]
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hxA' : x ∈ closure (interior A) := hA hxA
      -- Show the needed inclusion on closures
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hsubset hxA'
  | inr hxB =>
      -- `x ∈ B`
      have hxB' : x ∈ closure (interior B) := hB hxB
      -- Show the needed inclusion on closures
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hxB'

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {A : ι → Set X} (h : ∀ i, P3 (A i)) : P3 (⋃ i, A i) := by
  dsimp [P3] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_in : x ∈ interior (closure (A i)) := (h i) hx_i
  have h_subset : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    apply interior_mono
    exact closure_mono (Set.subset_iUnion _ _)
  exact h_subset hx_in

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} (h : ∀ A ∈ S, P2 A) : P2 (⋃₀ S) := by
  dsimp [P2] at h ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : P2 A := h A hA_mem
  have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ S))) := by
    apply interior_mono
    have hclosure :
        closure (interior A) ⊆ closure (interior (⋃₀ S)) := by
      apply closure_mono
      -- `interior A ⊆ interior (⋃₀ S)`
      have hinterior :
          interior A ⊆ interior (⋃₀ S) := by
        -- `interior A` is open and contained in `⋃₀ S`
        have hsub : (interior A : Set X) ⊆ ⋃₀ S := by
          intro y hy
          have hyA : y ∈ A := interior_subset hy
          exact Set.mem_sUnion.2 ⟨A, hA_mem, hyA⟩
        exact interior_maximal hsub isOpen_interior
      exact hinterior
    exact hclosure
  exact hsubset hx_in