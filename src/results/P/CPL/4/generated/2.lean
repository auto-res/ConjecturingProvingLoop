

theorem P1_closed_iff_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P1 A ↔ A = closure (interior A) := by
  simpa [hA.closure_eq, eq_comm] using
    (P1_iff_closure_interior_eq_closure (X := X) (A := A))

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  refine
    Set.Subset.trans hP2
      (interior_mono
        (closure_mono (interior_subset : (interior A : Set X) ⊆ A)))

theorem P2_Union_family {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (h : ∀ i, Topology.P2 (s i)) : Topology.P2 (⋃ i, s i) := by
  dsimp [Topology.P2] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : (s i : Set X) ⊆ interior (closure (interior (s i))) := h i
  have hx₁ : x ∈ interior (closure (interior (s i))) := hPi hxi
  have h_int_mono : interior (s i) ⊆ interior (⋃ j, s j) :=
    interior_mono (Set.subset_iUnion _ _)
  have h_closure_mono :
      closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) :=
    closure_mono h_int_mono
  have h_interior_mono :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) :=
    interior_mono h_closure_mono
  exact h_interior_mono hx₁

theorem P3_iUnion_directed {ι : Sort _} {X : Type*} [TopologicalSpace X] (s : ι → Set X) (hdir : Directed (· ⊆ ·) s) (h : ∀ i, Topology.P3 (s i)) : Topology.P3 (⋃ i, s i) := by
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hPi : (s i : Set X) ⊆ interior (closure (s i)) := h i
  have hx₁ : x ∈ interior (closure (s i)) := hPi hxi
  have h_closure_mono : (closure (s i) : Set X) ⊆ closure (⋃ j, s j) :=
    closure_mono (Set.subset_iUnion _ _)
  have h_interior_mono :
      interior (closure (s i)) ⊆ interior (closure (⋃ j, s j)) :=
    interior_mono h_closure_mono
  exact h_interior_mono hx₁

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : Homeomorph X Y) {A : Set X} (hA : Topology.P3 A) : Topology.P3 (e '' A) := by
  -- Expand the definition of `P3`
  dsimp [Topology.P3] at hA ⊢
  intro y hy
  -- Choose a preimage point `x ∈ A` with `y = e x`
  rcases hy with ⟨x, hxA, rfl⟩
  -- From the hypothesis we know that `x` lies in `interior (closure A)`
  have hx : x ∈ interior (closure A) := hA hxA
  ----------------------------------------------------------------
  -- 1.  The auxiliary set `S = e '' interior (closure A)` is open
  ----------------------------------------------------------------
  have hS_open : IsOpen (e '' interior (closure A)) := by
    -- Identify `S` with a preimage under the continuous map `e.symm`
    have h_eq :
        (e '' interior (closure A) : Set _) =
          { y | e.symm y ∈ interior (closure A) } := by
      ext y
      constructor
      · rintro ⟨x, hx', rfl⟩
        simp [hx']
      · intro hy
        refine ⟨e.symm y, ?_, ?_⟩
        · simpa using hy
        · simpa using e.apply_symm_apply y
    -- The right-hand side is a preimage of an open set under a continuous map
    have h_pre :
        IsOpen { y | e.symm y ∈ interior (closure A) } := by
      have h_int_open : IsOpen (interior (closure A)) := isOpen_interior
      simpa [Set.preimage] using h_int_open.preimage e.symm.continuous
    simpa [h_eq] using h_pre
  ----------------------------------------------------------------
  -- 2.  `S` is contained in `closure (e '' A)`
  ----------------------------------------------------------------
  have hS_subset : (e '' interior (closure A) : Set _) ⊆ closure (e '' A) := by
    intro z hz
    rcases hz with ⟨x', hx'int, rfl⟩
    -- `x'` lies in `closure A`
    have hx'cl : x' ∈ closure A := interior_subset hx'int
    -- Show `e x'` is in the closure of the image
    have : e x' ∈ closure (e '' A) := by
      -- Neighbourhood characterisation of the closure
      apply (mem_closure_iff).2
      intro V hVopen hVmem
      -- Preimage of `V` under `e`
      have hUopen : IsOpen (e ⁻¹' V) := hVopen.preimage e.continuous
      have hxU : x' ∈ e ⁻¹' V := by
        simpa [Set.mem_preimage] using hVmem
      -- Since `x' ∈ closure A`, the intersection with `A` is non-empty
      have h_nonempty_pre : ((e ⁻¹' V) ∩ A).Nonempty := by
        have h_closure := (mem_closure_iff).1 hx'cl
        exact h_closure (e ⁻¹' V) hUopen hxU
      -- Map a witness through `e`
      rcases h_nonempty_pre with ⟨w, ⟨hw_preV, hwA⟩⟩
      have hwV : e w ∈ V := by
        simpa [Set.mem_preimage] using hw_preV
      have hwIm : e w ∈ e '' A := ⟨w, hwA, rfl⟩
      exact ⟨e w, And.intro hwV hwIm⟩
    exact this
  ----------------------------------------------------------------
  -- 3.  Maximality of the interior
  ----------------------------------------------------------------
  have hS_in_interior :
      (e '' interior (closure A) : Set _) ⊆
        interior (closure (e '' A)) :=
    interior_maximal hS_subset hS_open
  ----------------------------------------------------------------
  -- 4.  Our point belongs to `S`, hence to the desired interior
  ----------------------------------------------------------------
  have hy_in_S : e x ∈ e '' interior (closure A) := ⟨x, hx, rfl⟩
  exact hS_in_interior hy_in_S