

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : Homeomorph X Y) {A : Set X} (hA : Topology.P1 A) : Topology.P1 (e '' A) := by
  -- Unfold the definition of `P1`
  dsimp [Topology.P1] at hA ⊢
  -- Take a point of the image
  rintro y ⟨x, hxA, rfl⟩
  -- `x` lies in the closure of `interior A`
  have hx_cl : (x : X) ∈ closure (interior A) := hA hxA
  ----------------------------------------------------------------
  -- Auxiliary open set `S = e '' interior A`
  ----------------------------------------------------------------
  let S : Set Y := e '' interior A
  have hS_open : IsOpen (S) := by
    -- Identify `S` with a preimage of an open set under `e.symm`
    have h_eq : (S : Set Y) = { y | e.symm y ∈ interior A } := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simp [hw]
      · intro hz
        refine ⟨e.symm z, ?_, ?_⟩
        · simpa using hz
        · simpa using e.apply_symm_apply z
    -- The right-hand side is open as the preimage of an open set
    have h_pre :
        IsOpen { y | e.symm y ∈ interior A } := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [Set.preimage] using this.preimage e.symm.continuous
    simpa [h_eq] using h_pre
  ----------------------------------------------------------------
  -- `S` is contained in `interior (e '' A)`
  ----------------------------------------------------------------
  have hS_subset : (S : Set Y) ⊆ interior (e '' A) := by
    -- First, `S ⊆ e '' A`
    have hS_sub : (S : Set Y) ⊆ e '' A := by
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact ⟨w, interior_subset hw, rfl⟩
    -- Maximality of the interior
    simpa using interior_maximal hS_sub hS_open
  ----------------------------------------------------------------
  -- Show `e x ∈ closure S`
  ----------------------------------------------------------------
  have h_ex_closure_S : e x ∈ closure (S) := by
    -- Use the filter characterisation of the closure
    apply (mem_closure_iff).2
    intro V hV_open hxV
    -- Preimage of `V` under `e`
    let U : Set X := e ⁻¹' V
    have hU_open : IsOpen U := hV_open.preimage e.continuous
    have hxU : x ∈ U := by
      change e x ∈ V at hxV
      simpa [U, Set.mem_preimage] using hxV
    -- `U ∩ interior A` is non-empty
    have h_nonempty : (U ∩ interior A).Nonempty := by
      have := (mem_closure_iff).1 hx_cl U hU_open hxU
      simpa [U] using this
    rcases h_nonempty with ⟨w, hwU, hw_int⟩
    -- Produce the required witness in `V ∩ S`
    have hwV : e w ∈ V := by
      have : w ∈ U := hwU
      simpa [U, Set.mem_preimage] using this
    have hwS : e w ∈ S := by
      exact ⟨w, hw_int, rfl⟩
    exact ⟨e w, And.intro hwV hwS⟩
  ----------------------------------------------------------------
  -- Monotonicity of the closure finishes the proof
  ----------------------------------------------------------------
  have h_closure_mono :
      closure (S) ⊆ closure (interior (e '' A)) :=
    closure_mono hS_subset
  exact h_closure_mono h_ex_closure_S

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : Homeomorph X Y) {A : Set X} (hA : Topology.P2 A) : Topology.P2 (e '' A) := by
  -- `A` satisfies both `P1` and `P3`, hence so does its image
  have hP1_img : Topology.P1 (e '' A) :=
    P1_image_homeomorph (e := e) (P2_implies_P1 (A := A) hA)
  have hP3_img : Topology.P3 (e '' A) :=
    P3_image_homeomorph (e := e) (P2_implies_P3 (A := A) hA)
  -- Use the characterisation `P2 ↔ P1 ∧ P3`
  exact (P2_iff_P1_and_P3 (A := e '' A)).2 ⟨hP1_img, hP3_img⟩

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : Homeomorph X Y) {B : Set Y} (hB : Topology.P3 B) : Topology.P3 (e ⁻¹' B) := by
  -- First, identify the preimage with the image under `e.symm`.
  have h_preimage : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa [Set.mem_preimage, e.apply_symm_apply] using hyB
    · intro hx
      refine ⟨e x, ?_, ?_⟩
      · simpa [Set.mem_preimage] using hx
      · simpa using e.symm_apply_apply x
  -- Apply the image lemma for `e.symm` and rewrite using the equality above.
  have hP3 : Topology.P3 (e.symm '' B) :=
    P3_image_homeomorph (e := e.symm) (A := B) hB
  simpa [h_preimage] using hP3

theorem openSet_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  -- `A` is an open neighbourhood of `x`
  have h_nhds : (closure (A : Set X)) ∈ 𝓝 x := by
    have h_mem : (A : Set X) ∈ 𝓝 x := IsOpen.mem_nhds hA hx
    exact Filter.mem_of_superset h_mem (subset_closure : (A : Set X) ⊆ closure A)
  have hx_int : x ∈ interior (closure A) :=
    (mem_interior_iff_mem_nhds).2 h_nhds
  simpa [hA.interior_eq] using hx_int