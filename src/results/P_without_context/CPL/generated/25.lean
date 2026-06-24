

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro h
  exact Set.Subset.trans h interior_subset

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  dsimp [P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hAx =>
      exact
        (closure_mono (interior_mono Set.subset_union_left)) (hA hAx)
  | inr hBx =>
      exact
        (closure_mono (interior_mono Set.subset_union_right)) (hB hBx)

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  dsimp [P3]
  intro x hx
  have h : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  exact h hx

theorem open_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  dsimp [P2]
  intro x hx
  -- `A` is contained in the interior of its closure because it is open
  have h_subset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  -- `x` belongs to that interior
  have hx' : x ∈ interior (closure A) := h_subset hx
  -- rewrite `interior A` using the openness of `A`
  have hInt : interior A = A := hA.interior_eq
  simpa [hInt] using hx'

theorem P2_iff_exists_open_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ closure U = closure (interior A) := by
  dsimp [P2]
  constructor
  · intro hP2
    refine
      ⟨interior (closure (interior A)), isOpen_interior, hP2, ?_⟩
    -- We prove the required equality of closures.
    have h₁ : (interior (closure (interior A)) : Set X) ⊆ closure (interior A) :=
      interior_subset
    have h₂ : (interior A : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal subset_closure isOpen_interior
    have h_closure₁ : closure (interior (closure (interior A))) ⊆
        closure (interior A) := by
      -- `closure_mono` together with `closure_closure`
      have := closure_mono h₁
      simpa [closure_closure] using this
    have h_closure₂ : closure (interior A) ⊆
        closure (interior (closure (interior A))) := by
      have := closure_mono h₂
      simpa using this
    exact Set.Subset.antisymm h_closure₁ h_closure₂
  · rintro ⟨U, hUopen, hAU, hClosure⟩
    -- We obtain the desired inclusion `A ⊆ interior (closure (interior A))`.
    have hU_in : (U : Set X) ⊆ interior (closure U) :=
      interior_maximal subset_closure hUopen
    have hA_in : (A : Set X) ⊆ interior (closure U) :=
      Set.Subset.trans hAU hU_in
    simpa [hClosure] using hA_in

theorem P3_closed_under_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, P3 A) → P3 (⋃₀ 𝒜) := by
  dsimp [P3]
  intro h
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : P3 A := h A hA_mem
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  have h_subset :
      (interior (closure A) : Set X) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono (closure_mono (Set.subset_sUnion_of_mem hA_mem))
  exact h_subset hx_int