

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P1 A := by
  intro x hx
  exact
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
      (hA hx)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_cl : x ∈ closure (interior A) := hA hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inl hy))
      exact hsubset hx_cl
  | inr hxB =>
      -- `x` comes from `B`
      have hx_cl : x ∈ closure (interior B) := hB hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inr hy))
      exact hsubset hx_cl

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h𝒜 : ∀ A ∈ 𝒜, P3 A) : P3 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hx_int : x ∈ interior (closure A) := (h𝒜 A hA_mem) hxA
  have hsubset : closure A ⊆ closure (⋃₀ 𝒜) := closure_mono <| by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  exact (interior_mono hsubset) hx_int

theorem exists_P3_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ B : Set X, A ⊆ B ∧ P3 B := by
  refine ⟨Set.univ, ?_, ?_⟩
  · intro x hx
    exact Set.mem_univ x
  · intro x hx
    simpa [closure_univ, interior_univ] using hx