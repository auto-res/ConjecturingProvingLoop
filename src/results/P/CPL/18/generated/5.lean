

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  dsimp [Topology.P2, Topology.P3]
  -- `A` is closed, so its closure is itself
  have h_closure : (closure (A : Set X)) = A := hA.closure_eq
  constructor
  · intro hP2
    -- first, relate the two interiors that appear
    have h_closure_mono : closure (interior A) ⊆ closure A := by
      apply closure_mono
      exact interior_subset
    have h_int_mono : interior (closure (interior A)) ⊆ interior A := by
      have h := interior_mono h_closure_mono
      simpa [h_closure] using h
    -- chain the inclusions
    have : A ⊆ interior A := Set.Subset.trans hP2 h_int_mono
    simpa [h_closure] using this
  · intro hP3
    -- `interior A` is open and contained in its closure, hence in the interior
    -- of that closure
    have h_sub : interior A ⊆ interior (closure (interior A)) :=
      interior_maximal
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior
    -- chain the inclusions
    have : A ⊆ interior A := by
      simpa [h_closure] using hP3
    exact Set.Subset.trans this h_sub

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  -- From the density hypothesis we get that the closure is the whole space
  have h_closure : closure (interior (A : Set X)) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; simp
    · intro _; exact h y
  -- Hence its interior is also the whole space, so the desired membership is trivial
  simpa [h_closure, interior_univ] using (by
    have : x ∈ (Set.univ : Set X) := by simp
    exact this)

theorem exists_P2_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, A ⊆ U ∧ Topology.P2 U := by
  rcases exists_open_subset_P2 (A := A) with ⟨U, _hUopen, hAU, hP2U⟩
  exact ⟨U, hAU, hP2U⟩

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P3 A) : Topology.P3 (⋃₀ 𝒜) := by
  dsimp [Topology.P3] at h ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : Topology.P3 A := h A hA_mem
  have hx' : x ∈ interior (closure A) := hP3A hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion_of_mem hy hA_mem
  exact hsubset hx'

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P1 A) : Topology.P1 (⋃₀ 𝒜) := by
  dsimp [Topology.P1] at h ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A : Topology.P1 A := h A hA_mem
  have hx' : x ∈ closure (interior A) := hP1A hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion_of_mem hy hA_mem
  exact hsubset hx'

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  exact Set.empty_subset _