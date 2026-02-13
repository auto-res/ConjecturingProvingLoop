

theorem open_iff_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  -- For an open set `A`, `P2 A` always holds.
  have hP2 : Topology.P2 A := P2_of_open hA
  constructor
  · intro _hP1
    -- Hence `P3 A` holds via `P3_of_P2`.
    exact P3_of_P2 hP2
  · intro _hP3 x hx
    -- Since `A` is open, `x ∈ interior A`.
    have hx_int : x ∈ interior A := by
      simpa [hA.interior_eq] using hx
    -- The closure contains its interior.
    exact subset_closure hx_int

theorem closed_iff_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · exact P3_of_P2
  · intro hP3
    intro x hx
    -- First, rewrite `P3` using the fact that `A` is closed.
    have hx_intA : x ∈ interior A := by
      have : x ∈ interior (closure A) := hP3 hx
      simpa [hA.closure_eq] using this
    -- Next, use monotonicity of `interior` to upgrade the membership.
    have hsubset : interior A ⊆ interior (closure (interior A)) := by
      have : interior (interior A) ⊆ interior (closure (interior A)) :=
        interior_mono (subset_closure : interior A ⊆ closure (interior A))
      simpa [interior_interior] using this
    exact hsubset hx_intA

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} : (∀ A ∈ 𝒜, Topology.P2 A) → Topology.P2 (⋃₀ 𝒜) := by
  intro hP2
  intro x hx
  -- Pick a set `A` in `𝒜` that contains `x`.
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- Apply `P2` to that particular set.
  have hP2A : Topology.P2 A := hP2 A hA_mem
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  -- Relate the corresponding interiors/closures to those of `⋃₀ 𝒜`.
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    -- `A ⊆ ⋃₀ 𝒜`
    have h_sub : (A : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    -- Monotonicity of `interior` and `closure`.
    have h_int_sub : interior A ⊆ interior (⋃₀ 𝒜) := interior_mono h_sub
    have h_cl_sub :
        closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono h_int_sub
    exact interior_mono h_cl_sub
  exact h_subset hx_int