

theorem P2_iSup_family {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} : (∀ i, P2 (F i)) → P2 (⋃ i, F i) := by
  intro h
  ------------------------------------------------------------------
  -- 1.  Every set in `Set.range F` satisfies `P2`.
  ------------------------------------------------------------------
  have hAll : ∀ A : Set X, A ∈ Set.range F → P2 A := by
    intro A hA
    rcases hA with ⟨i, rfl⟩
    exact h i
  ------------------------------------------------------------------
  -- 2.  Apply the `sUnion` lemma for `P2`.
  ------------------------------------------------------------------
  have hP2_range : P2 (⋃₀ Set.range F) :=
    P2_sUnion (X := X) (𝒜 := Set.range F) hAll
  ------------------------------------------------------------------
  -- 3.  Identify `⋃₀ Set.range F` with `⋃ i, F i`.
  ------------------------------------------------------------------
  have h_eq : (⋃₀ Set.range F : Set X) = ⋃ i, F i := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
      rcases hA_mem with ⟨i, rfl⟩
      exact Set.mem_iUnion.2 ⟨i, hxA⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
      exact Set.mem_sUnion.2 ⟨F i, ⟨i, rfl⟩, hxFi⟩
  ------------------------------------------------------------------
  -- 4.  Transfer the result through the equality.
  ------------------------------------------------------------------
  simpa [h_eq] using hP2_range

theorem P1_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → interior (closure A) ⊆ closure (interior A) := by
  intro hP1
  intro x hx
  -- `x` lies in `closure A` because it lies in `interior (closure A)`.
  have hx_clA : x ∈ closure A := interior_subset hx
  -- From `P1 A`, we have `A ⊆ closure (interior A)`.
  -- Taking closures preserves inclusions.
  have h_subset : closure A ⊆ closure (interior A) := by
    have hA : (A : Set X) ⊆ closure (interior A) := hP1
    have h' : closure A ⊆ closure (closure (interior A)) :=
      closure_mono hA
    simpa [closure_closure] using h'
  exact h_subset hx_clA

theorem P2_union₃ {X : Type*} [TopologicalSpace X] {A B C : Set X} : P2 A → P2 B → P2 C → P2 (A ∪ B ∪ C) := by
  intro hP2A hP2B hP2C
  have hAB : P2 (A ∪ B) := P2_union hP2A hP2B
  have hABC : P2 ((A ∪ B) ∪ C) := P2_union hAB hP2C
  simpa [Set.union_assoc] using hABC