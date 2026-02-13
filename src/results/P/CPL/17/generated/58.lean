

theorem P2_diff {X : Type*} [TopologicalSpace X] {A B : Set X} : Topology.P2 A → IsClosed B → Topology.P2 (A \ B) := by
  intro hP2A hB_closed
  intro x hx
  -- Decompose the membership `x ∈ A \ B`
  have hxA   : x ∈ A := hx.1
  have hxNot : x ∉ B := hx.2
  -- From `P2` for `A`
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  -- Two auxiliary open sets
  have hO₁ : IsOpen (interior (closure (interior A))) := isOpen_interior
  have hO₂ : IsOpen (Bᶜ : Set X) := (isOpen_compl_iff).2 hB_closed
  -- The open neighbourhood we will use
  let W : Set X := interior (closure (interior A)) ∩ Bᶜ
  have hW_open : IsOpen W := hO₁.inter hO₂
  have hxW : x ∈ W := by
    exact ⟨hx_int, hxNot⟩
  -- Show `W ⊆ closure (interior (A \ B))`
  have hW_sub : (W : Set X) ⊆ closure (interior (A \ B)) := by
    intro y hyW
    have hy_intCl : y ∈ interior (closure (interior A)) := hyW.1
    have hy_notB  : y ∈ Bᶜ := hyW.2
    have hy_cl    : y ∈ closure (interior A) :=
      (interior_subset :
        interior (closure (interior A)) ⊆ closure (interior A)) hy_intCl
    -- Use the neighbourhood criterion for closure
    have : y ∈ closure (interior (A \ B)) := by
      refine (mem_closure_iff).2 ?_
      intro V hV_open hyV
      -- Work inside `V ∩ Bᶜ`
      have hVB_open : IsOpen (V ∩ Bᶜ) := hV_open.inter hO₂
      have hy_VB : y ∈ V ∩ Bᶜ := ⟨hyV, hy_notB⟩
      -- `interior A` meets `V ∩ Bᶜ`
      have h_nonempty :=
        (mem_closure_iff).1 hy_cl (V ∩ Bᶜ) hVB_open hy_VB
      rcases h_nonempty with ⟨z, hz_VB, hz_intA⟩
      -- Split the information on `z`
      have hzV    : z ∈ V := hz_VB.1
      have hz_notB: z ∈ Bᶜ := hz_VB.2
      -- `z` lies in `interior (A \ B)`
      have hz_intDiff : z ∈ interior (A \ B) := by
        -- The open set `interior A ∩ Bᶜ`
        have h_open_aux : IsOpen (interior A ∩ Bᶜ) :=
          (isOpen_interior).inter hO₂
        have hz_aux_in : z ∈ interior A ∩ Bᶜ := ⟨hz_intA, hz_notB⟩
        have h_sub_aux :
            (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
          intro w hw
          exact ⟨(interior_subset : interior A ⊆ A) hw.1, hw.2⟩
        exact (interior_maximal h_sub_aux h_open_aux) hz_aux_in
      exact ⟨z, ⟨hzV, hz_intDiff⟩⟩
    exact this
  -- An open subset of a closure sits in the interior of that closure
  have hW_int :
      (W : Set X) ⊆ interior (closure (interior (A \ B))) :=
    interior_maximal hW_sub hW_open
  -- Finish
  exact hW_int hxW

theorem P1_nhds_iff {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ (∀ x ∈ A, ∀ U ∈ 𝓝 x, (U ∩ interior A).Nonempty) := by
  classical
  constructor
  · intro hP1 x hxA U hU
    -- `x` lies in the closure of `interior A`
    have hx_cl : x ∈ closure (interior A) := hP1 hxA
    -- Choose an open neighbourhood `V` of `x` contained in `U`
    rcases mem_nhds_iff.1 hU with ⟨V, hV_sub, hV_open, hxV⟩
    -- `V` meets `interior A`
    have hV_int : (V ∩ interior A).Nonempty :=
      (mem_closure_iff).1 hx_cl V hV_open hxV
    -- Hence so does `U`
    rcases hV_int with ⟨y, hyV, hyIntA⟩
    exact ⟨y, ⟨hV_sub hyV, hyIntA⟩⟩
  · intro h x hxA
    -- Show that every open neighbourhood of `x` meets `interior A`
    have h_cl :
        ∀ V, IsOpen V → x ∈ V → (V ∩ interior A).Nonempty := by
      intro V hV_open hxV
      have hV_nhds : (V : Set X) ∈ 𝓝 x := hV_open.mem_nhds hxV
      exact h x hxA V hV_nhds
    -- Conclude `x ∈ closure (interior A)`
    exact (mem_closure_iff).2 h_cl

theorem P3_sdiff {X : Type*} [TopologicalSpace X] {A B : Set X} : Topology.P3 A → IsClosed B → Topology.P3 (A \ B) := by
  intro hP3A hB_closed
  intro x hx
  -- Decompose the hypothesis `x ∈ A \ B`.
  have hxA : x ∈ A := hx.1
  have hxNotB : x ∉ B := hx.2
  -- From `P3 A` we obtain `x ∈ interior (closure A)`.
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  -- The complement of `B` is open.
  have h_open_Bc : IsOpen (Bᶜ : Set X) := (isOpen_compl_iff).2 hB_closed
  -- The open set we shall use.
  let U : Set X := interior (closure A) ∩ Bᶜ
  have hU_open : IsOpen U :=
    (isOpen_interior).inter h_open_Bc
  have hxU : x ∈ U := by
    dsimp [U]
    exact ⟨hx_int, by
      -- `x ∈ Bᶜ` is definitionally `x ∉ B`.
      simpa using hxNotB⟩
  -- Show that `U ⊆ closure (A \ B)`.
  have hU_sub : (U : Set X) ⊆ closure (A \ B) := by
    intro y hy
    rcases hy with ⟨hy_int, hy_notB⟩
    -- `y` lies in `closure A`.
    have hy_clA : y ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hy_int
    -- Prove `y ∈ closure (A \ B)` using the neighbourhood criterion.
    have : y ∈ closure (A \ B) := by
      apply (mem_closure_iff).2
      intro V hV_open hyV
      -- Work inside `V ∩ Bᶜ`.
      have hVB_open : IsOpen (V ∩ Bᶜ) := hV_open.inter h_open_Bc
      have hy_VB : y ∈ V ∩ Bᶜ := ⟨hyV, hy_notB⟩
      -- Since `y ∈ closure A`, `A` meets `V ∩ Bᶜ`.
      have h_nonempty :=
        (mem_closure_iff).1 hy_clA (V ∩ Bᶜ) hVB_open hy_VB
      rcases h_nonempty with ⟨z, hz_VB, hzA⟩
      -- `z` lies in `V ∩ (A \ B)`.
      have hz_mem : z ∈ V ∩ (A \ B) := by
        rcases hz_VB with ⟨hzV, hz_notB⟩
        exact ⟨hzV, ⟨hzA, hz_notB⟩⟩
      exact ⟨z, hz_mem⟩
    exact this
  -- An open subset of a closure lies in the corresponding interior.
  have hU_int : (U : Set X) ⊆ interior (closure (A \ B)) :=
    interior_maximal hU_sub hU_open
  -- Conclude: `x ∈ interior (closure (A \ B))`.
  exact hU_int hxU