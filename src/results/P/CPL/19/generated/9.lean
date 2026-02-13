

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  intro x hx
  -- `closure A ⊆ closure (interior A)`
  have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
    simpa [closure_closure] using closure_mono hP1
  -- `closure (interior A) ⊆ closure (interior (closure A))`
  have h₂ :
      closure (interior A) ⊆ closure (interior (closure (A : Set X))) := by
    have hsubset : interior A ⊆ interior (closure (A : Set X)) := by
      apply interior_mono
      exact subset_closure
    exact closure_mono hsubset
  exact h₂ (h₁ hx)

theorem P1_Union_family {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} (h : ∀ i, P1 (F i)) : P1 (⋃ i, F i) := by
  -- First, show every set in `Set.range F` satisfies `P1`.
  have hAll : ∀ A : Set X, A ∈ Set.range F → P1 A := by
    intro A hA
    rcases hA with ⟨i, rfl⟩
    exact h i
  -- Apply the `sUnion` lemma.
  have hP1_range : P1 (⋃₀ Set.range F) :=
    P1_sUnion (X := X) (𝒜 := Set.range F) hAll
  -- Identify `⋃₀ Set.range F` with `⋃ i, F i`.
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
  simpa [h_eq] using hP1_range

theorem P3_iSup_family {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} (h : ∀ i, P3 (F i)) : P3 (⋃ i, F i) := by
  -- First, show every set in `Set.range F` satisfies `P3`.
  have hAll : ∀ A : Set X, A ∈ Set.range F → P3 A := by
    intro A hA
    rcases hA with ⟨i, rfl⟩
    exact h i
  -- Apply the `sUnion` lemma.
  have hP3_range : P3 (⋃₀ Set.range F) :=
    P3_sUnion (X := X) (𝒜 := Set.range F) hAll
  -- Identify `⋃₀ Set.range F` with `⋃ i, F i`.
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
  simpa [h_eq] using hP3_range

theorem P2_of_P3_and_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A → P2 A := by
  intro hA hP3
  exact ((P2_iff_P3_of_open (X := X) (A := A) hA).2) hP3