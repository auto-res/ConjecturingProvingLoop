

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact P1_implies_dense (A := A) hP1
  · intro h_eq
    intro x hx
    have hmem : x ∈ closure A := subset_closure hx
    simpa [h_eq] using hmem

theorem P2_subset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono (interior_subset : interior A ⊆ A))
  exact hsubset hx₁

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (interior A) := by
  intro _hP1
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  constructor
  ·
    exact P2_subset_P3 (A := A)
  ·
    intro hP3
    -- Show `A ⊆ interior A`
    have hsubset : (A : Set X) ⊆ interior A := by
      intro x hx
      have : x ∈ interior (closure A) := hP3 hx
      simpa [hA.closure_eq] using this
    -- Hence `interior A = A`
    have hInt_eq : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact hsubset
    -- Therefore `A` is open
    have hA_open : IsOpen A := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [hInt_eq] using this
    -- Apply the open-set version of `P2`
    exact P2_of_open hA_open

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A, A ∈ 𝒜 → P1 A) → P1 (⋃₀ 𝒜) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A : P1 A := hAll A hA_mem
  have hx_closure : x ∈ closure (interior A) := hP1A hxA
  have hA_subset_union : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro z hz
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hz⟩
  have hsubset_interior : interior A ⊆ interior (⋃₀ 𝒜) :=
    interior_mono hA_subset_union
  have hsubset_closure :
      closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono hsubset_interior
  exact hsubset_closure hx_closure

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A, A ∈ 𝒜 → P2 A) → P2 (⋃₀ 𝒜) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : P2 A := hAll A hA_mem
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  have hsubset_interior : interior A ⊆ interior (⋃₀ 𝒜) := by
    apply interior_mono
    intro z hz
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hz⟩
  have hsubset_closure :
      closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono hsubset_interior
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) :=
    interior_mono hsubset_closure
  exact hsubset hx_int

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A, A ∈ 𝒜 → P3 A) → P3 (⋃₀ 𝒜) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : P3 A := hAll A hA_mem
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  have hsubset_closure : closure A ⊆ closure (⋃₀ 𝒜) := by
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono hsubset_closure
  exact hsubset hx_int

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx