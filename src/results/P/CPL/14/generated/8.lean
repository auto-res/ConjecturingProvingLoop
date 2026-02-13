

theorem P1_sUnion {X} [TopologicalSpace X] {ℱ : Set (Set X)} (h : ∀ A ∈ ℱ, P1 A) : P1 (⋃₀ ℱ) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℱ, hxA⟩
  have hP1A : P1 A := h A hAℱ
  have hx_cl : x ∈ closure (interior A) := hP1A hxA
  have hsubset_int : interior A ⊆ interior (⋃₀ ℱ) :=
    interior_mono (Set.subset_sUnion_of_mem hAℱ)
  have hsubset_cl : closure (interior A) ⊆ closure (interior (⋃₀ ℱ)) :=
    closure_mono hsubset_int
  exact hsubset_cl hx_cl

theorem P1_iff_closure_interior {X} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  unfold P1
  constructor
  · intro hP1
    -- We always have `closure (interior A) ⊆ closure A`.
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    -- From `A ⊆ closure (interior A)`, taking closures yields the reverse inclusion.
    have h₂ : closure A ⊆ closure (interior A) := by
      have : closure A ⊆ closure (closure (interior A)) :=
        closure_mono hP1
      simpa [closure_closure] using this
    exact Set.Subset.antisymm h₁ h₂
  · intro hEq
    -- Since `A ⊆ closure A` and the closures are equal, the desired inclusion holds.
    have : A ⊆ closure A := subset_closure
    simpa [hEq] using this