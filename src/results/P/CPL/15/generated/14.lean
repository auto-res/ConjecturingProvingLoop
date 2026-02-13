

theorem P3_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (h : P3 A) : P3 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` is in the interior of the closure of `A`
  have hx_int : x ∈ interior (closure A) := h hxA
  rcases mem_interior.1 hx_int with ⟨U, hU_sub, hU_open, hxU⟩
  -- The image of `U` is an open neighbourhood of `e x`
  have hV_open : IsOpen (e '' U) := by
    -- identify `e '' U` with a preimage under `e.symm`
    have h_eq : (e '' U : Set Y) = e.symm ⁻¹' U := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨u, huU, rfl⟩
        simpa using huU
      · intro hy
        exact ⟨e.symm y, hy, by simp⟩
    have h_pre : IsOpen (e.symm ⁻¹' U) := hU_open.preimage e.symm.continuous
    simpa [h_eq] using h_pre
  -- this image is contained in the desired closure
  have hV_sub : (e '' U : Set Y) ⊆ closure (e '' A) := by
    intro z hz
    rcases hz with ⟨u, huU, rfl⟩
    have hu_cl : (u : X) ∈ closure A := hU_sub huU
    -- prove `e u` is in the closure of `e '' A`
    have : (e u) ∈ closure (e '' A) := by
      refine (mem_closure_iff).2 ?_
      intro V hV_open hVu
      -- pull `V` back via `e`
      have h_pre_open : IsOpen (e ⁻¹' V) := hV_open.preimage e.continuous
      have h_pre_mem : u ∈ e ⁻¹' V := hVu
      obtain ⟨w, hw_pre, hwA⟩ :=
        (mem_closure_iff).1 hu_cl (e ⁻¹' V) h_pre_open h_pre_mem
      refine ⟨e w, ?_⟩
      have hwV : e w ∈ V := by
        have : w ∈ e ⁻¹' V := hw_pre
        simpa [Set.mem_preimage] using this
      have hwImg : e w ∈ e '' A := ⟨w, hwA, rfl⟩
      exact And.intro hwV hwImg
    exact this
  have h_mem : (e x) ∈ e '' U := ⟨x, hxU, rfl⟩
  exact mem_interior.2 ⟨e '' U, hV_sub, hV_open, h_mem⟩

theorem closure_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : closure (interior A) ⊆ closure A := by
  exact closure_mono (interior_subset : interior A ⊆ A)

theorem P1_dense_iff {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `A ⊆ closure (interior A)` we deduce the desired inclusion on closures.
    have : (closure A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hP1
    simpa [closure_closure] using this
  · intro hsubset
    -- We show `A ⊆ closure (interior A)`
    intro x hx
    have hx_cl : (x : X) ∈ closure A := subset_closure hx
    exact hsubset hx_cl

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P2 A := by
  intro x hx
  classical
  -- In a subsingleton type, a non‐empty set must be the whole space.
  have hAu : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; simp
    · intro _
      have : y = x := Subsingleton.elim y x
      simpa [this] using hx
  -- Therefore the target set is `univ`, so the conclusion is immediate.
  simpa [hAu, interior_univ, closure_univ] using (Set.mem_univ x)