

theorem exists_open_dense_P3 {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ Dense U ∧ Topology.P3 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, dense_univ, ?_⟩
  simpa using (Topology.P3_univ (X := X))

theorem P1_union_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} {B : Set X} (hB : Topology.P1 B) (hS : ∀ A ∈ 𝒮, Topology.P1 A) : Topology.P1 (B ∪ ⋃₀ 𝒮) := by
  -- First obtain `P1` for the sUnion.
  have hSUnion : Topology.P1 (⋃₀ 𝒮) :=
    Topology.P1_sUnion (X := X) (𝒮 := 𝒮) hS
  -- Combine with `hB` using `P1_union`.
  simpa using
    (Topology.P1_union (A := B) (B := ⋃₀ 𝒮) hB hSUnion)

theorem P3_inter_open {X : Type*} [TopologicalSpace X] {A U : Set X} (hA : Topology.P3 A) (hU : IsOpen U) : Topology.P3 (A ∩ U) := by
  -- Unfold `P3` goal
  intro x hx
  -- `x` is in `A` and in the open set `U`
  have hxA : (x : X) ∈ A := hx.1
  have hxU : x ∈ U := hx.2
  -- From `P3 A` we get that `x ∈ interior (closure A)`
  have hxInt : (x : X) ∈ interior (closure A) := hA hxA
  --------------------------------------------------------------------
  --  Define an auxiliary open neighbourhood of `x`
  --------------------------------------------------------------------
  set S : Set X := interior (closure A) ∩ U with hS_def
  have hS_open : IsOpen S := isOpen_interior.inter hU
  have hxS : (x : X) ∈ S := by
    have : x ∈ interior (closure A) ∧ x ∈ U := ⟨hxInt, hxU⟩
    simpa [hS_def] using this
  --------------------------------------------------------------------
  --  Show that `S ⊆ closure (A ∩ U)`
  --------------------------------------------------------------------
  have hS_subset : (S : Set X) ⊆ closure (A ∩ U) := by
    intro y hyS
    have hyInt : y ∈ interior (closure A) := (by
      have h : y ∈ interior (closure A) ∧ y ∈ U := by
        simpa [hS_def] using hyS
      exact h.1)
    have hyU   : y ∈ U := (by
      have h : y ∈ interior (closure A) ∧ y ∈ U := by
        simpa [hS_def] using hyS
      exact h.2)
    -- We prove `y ∈ closure (A ∩ U)` via `mem_closure_iff`
    have : (y : X) ∈ closure (A ∩ U) := by
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- Consider the open set `V ∩ U`
      have hVU_open : IsOpen (V ∩ U) := hVopen.inter hU
      have hyVU : y ∈ V ∩ U := ⟨hyV, hyU⟩
      -- Since `y ∈ interior (closure A)`, hence `y ∈ closure A`
      have hy_clA : y ∈ closure A := interior_subset hyInt
      -- Thus `V ∩ U` meets `A`
      have h_nonempty : ((V ∩ U) ∩ A).Nonempty :=
        (mem_closure_iff).1 hy_clA (V ∩ U) hVU_open hyVU
      rcases h_nonempty with ⟨z, hzVU, hzA⟩
      -- Extract the components of `hzVU`
      have hzV : z ∈ V := hzVU.1
      have hzU : z ∈ U := hzVU.2
      -- Provide the witness that `V` meets `A ∩ U`
      exact ⟨z, hzV, ⟨hzA, hzU⟩⟩
    exact this
  --------------------------------------------------------------------
  --  `S` is an open neighbourhood of `x` contained in `closure (A ∩ U)`
  --  hence contained in its interior; conclude for `x`.
  --------------------------------------------------------------------
  have hS_int : (S : Set X) ⊆ interior (closure (A ∩ U)) :=
    interior_maximal hS_subset hS_open
  exact hS_int hxS