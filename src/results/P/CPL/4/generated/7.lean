

theorem openSet_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have hsubset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
  exact hsubset hx

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (Set.prod A B) := by
  -- Expand `P3` in the hypotheses and in the goal
  dsimp [Topology.P3] at hA hB ⊢
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Coordinate-wise use of the hypotheses
  have hx : p.1 ∈ interior (closure A) := hA hpA
  have hy : p.2 ∈ interior (closure B) := hB hpB
  ----------------------------------------------------------------
  -- 1.  The open rectangle
  ----------------------------------------------------------------
  have h_open :
      IsOpen (Set.prod (interior (closure A)) (interior (closure B))) := by
    have h1 : IsOpen (interior (closure A)) := isOpen_interior
    have h2 : IsOpen (interior (closure B)) := isOpen_interior
    simpa using h1.prod h2
  ----------------------------------------------------------------
  -- 2.  The rectangle is contained in `closure (A × B)`
  ----------------------------------------------------------------
  have h_subset :
      (Set.prod (interior (closure A)) (interior (closure B)) : Set (X × Y)) ⊆
        closure (Set.prod A B) := by
    intro q hq
    rcases hq with ⟨hq₁, hq₂⟩
    have hq1_cl : q.1 ∈ closure A := interior_subset hq₁
    have hq2_cl : q.2 ∈ closure B := interior_subset hq₂
    have h_mem_prod : (q : X × Y) ∈ Set.prod (closure A) (closure B) :=
      And.intro hq1_cl hq2_cl
    have h_eq :
        (closure (Set.prod A B) : Set (X × Y)) =
          Set.prod (closure A) (closure B) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod A B) = Set.prod (closure A) (closure B))
    simpa [h_eq] using h_mem_prod
  ----------------------------------------------------------------
  -- 3.  Maximality of the interior
  ----------------------------------------------------------------
  have h_interior :
      (Set.prod (interior (closure A)) (interior (closure B)) : Set (X × Y)) ⊆
        interior (closure (Set.prod A B)) :=
    interior_maximal h_subset h_open
  ----------------------------------------------------------------
  -- 4.  Our point lies in the rectangle, hence in the desired interior
  ----------------------------------------------------------------
  have hp_rect :
      p ∈ Set.prod (interior (closure A)) (interior (closure B)) :=
    And.intro hx hy
  exact h_interior hp_rect

theorem P1_sUnion_family {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P1 A) : Topology.P1 (⋃₀ 𝒜) := by
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hA_P1 : (A : Set X) ⊆ closure (interior A) := h A hA_mem
  have hx₁ : x ∈ closure (interior A) := hA_P1 hxA
  have hA_subset_sUnion : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have h_interior_subset :
      (interior A : Set X) ⊆ interior (⋃₀ 𝒜) :=
    interior_mono hA_subset_sUnion
  have h_closure_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_interior_subset
  exact h_closure_subset hx₁

theorem P3_sUnion_family {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P3 A) : Topology.P3 (⋃₀ 𝒜) := by
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hA_P3 : (A : Set X) ⊆ interior (closure A) := h A hA_mem
  have hx₁ : x ∈ interior (closure A) := hA_P3 hxA
  have hA_subset_sUnion : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have h_closure_subset :
      (closure A : Set X) ⊆ closure (⋃₀ 𝒜) :=
    closure_mono hA_subset_sUnion
  have h_interior_subset :
      (interior (closure A) : Set X) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono h_closure_subset
  exact h_interior_subset hx₁

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : Homeomorph X Y) {B : Set Y} (hB : Topology.P2 B) : Topology.P2 (e ⁻¹' B) := by
  -- `B` satisfies both `P1` and `P3`
  have hP1B : Topology.P1 B := P2_implies_P1 (A := B) hB
  have hP3B : Topology.P3 B := P2_implies_P3 (A := B) hB
  ----------------------------------------------------------------
  -- 1.  Identify the preimage with an image under `e.symm`
  ----------------------------------------------------------------
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa [Set.mem_preimage, e.apply_symm_apply] using hyB
    · intro hx
      refine ⟨e x, ?_, ?_⟩
      · simpa [Set.mem_preimage] using hx
      · simpa using e.symm_apply_apply x
  ----------------------------------------------------------------
  -- 2.  `P1` for the preimage
  ----------------------------------------------------------------
  have hP1_pre : Topology.P1 (e ⁻¹' B) := by
    have : Topology.P1 (e.symm '' B) :=
      P1_image_homeomorph (e := e.symm) (A := B) hP1B
    simpa [h_eq] using this
  ----------------------------------------------------------------
  -- 3.  `P3` for the preimage (already available)
  ----------------------------------------------------------------
  have hP3_pre : Topology.P3 (e ⁻¹' B) :=
    P3_preimage_homeomorph (e := e) (B := B) hP3B
  ----------------------------------------------------------------
  -- 4.  Combine via the characterisation of `P2`
  ----------------------------------------------------------------
  exact (P2_iff_P1_and_P3 (A := e ⁻¹' B)).2 ⟨hP1_pre, hP3_pre⟩

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  -- The closure of `interior A` is the whole space, by density.
  have h_closure : (closure (interior A) : Set X) = (Set.univ : Set X) :=
    h.closure_eq
  -- Hence its interior is also the whole space.
  have h_interior : (interior (closure (interior A)) : Set X) = Set.univ := by
    simpa [h_closure, interior_univ]
  -- The required inclusion now follows.
  simpa [h_interior] using (by
    trivial : x ∈ (Set.univ : Set X))