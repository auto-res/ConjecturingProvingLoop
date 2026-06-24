

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact hP2.trans interior_subset

theorem interior_has_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  dsimp [P2]
  simpa [interior_interior] using
    (interior_mono (subset_closure : interior A ⊆ closure (interior A)))

theorem IsOpen_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P2 A := by
  intro hA_open
  dsimp [P2]
  intro x hxA
  -- `A` itself is an open neighbourhood of `x`
  -- and it is contained in `closure (interior A)` because `A = interior A`.
  have h_subset : (A : Set X) ⊆ closure (interior A) := by
    simpa [hA_open.interior_eq] using
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
  have h_exists : ∃ t : Set X, t ⊆ closure (interior A) ∧ IsOpen t ∧ x ∈ t := by
    exact ⟨A, h_subset, hA_open, hxA⟩
  exact (mem_interior.2 h_exists)

theorem exists_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ B : Set X, B ⊆ A ∧ P1 B := by
  refine ⟨interior A, interior_subset, ?_⟩
  dsimp [P1]
  simpa [interior_interior] using
    (subset_closure : interior A ⊆ closure (interior A))

theorem union_P1 {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  dsimp [P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_cl : x ∈ closure (interior A) := hA hxA
      have h_subset : (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact h_subset hx_cl
  | inr hxB =>
      -- `x` comes from `B`
      have hx_cl : x ∈ closure (interior B) := hB hxB
      have h_subset : (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact h_subset hx_cl

theorem P3_iff_nhds {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A ↔ ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ closure A := by
  dsimp [P3]
  constructor
  · intro hP3 x hxA
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    rcases (mem_interior.1 hx_int) with ⟨U, hU_sub, hU_open, hxU⟩
    exact ⟨U, hU_open, hxU, hU_sub⟩
  · intro h x hxA
    rcases h x hxA with ⟨U, hU_open, hxU, hU_sub⟩
    exact (mem_interior.2 ⟨U, hU_sub, hU_open, hxU⟩)