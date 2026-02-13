

theorem P3_Union_finite {X : Type*} [TopologicalSpace X] {F : Finset (Set X)} : (∀ A ∈ F, Topology.P3 A) → Topology.P3 (⋃ A ∈ F, A) := by
  classical
  revert F
  intro F
  induction F using Finset.induction with
  | empty =>
      intro _hP3
      simpa using (P3_empty : Topology.P3 (∅ : Set X))
  | @insert A s hA_notin_s ih =>
      intro hF
      -- `P3` for the distinguished set `A`
      have hA : Topology.P3 A := by
        have : (A : Set X) ∈ (insert A s : Finset (Set X)) :=
          Finset.mem_insert_self A s
        exact hF A this
      -- `P3` for the union over the remaining sets, from the induction hypothesis
      have hF' : ∀ B, B ∈ s → Topology.P3 B := by
        intro B hB
        exact hF B (Finset.mem_insert_of_mem hB)
      have h_s : Topology.P3 (⋃ B ∈ s, (B : Set X)) := ih hF'
      -- Combine the two using a bespoke `P3`-union argument
      have h_union : Topology.P3 (A ∪ ⋃ B ∈ s, (B : Set X)) := by
        intro x hx
        cases hx with
        | inl hxA =>
            -- Case `x ∈ A`
            have hx_int : x ∈ interior (closure (A : Set X)) := hA hxA
            -- Monotonicity
            have hsubset :
                interior (closure (A : Set X)) ⊆
                  interior (closure (A ∪ ⋃ B ∈ s, (B : Set X))) := by
              apply interior_mono
              apply closure_mono
              intro y hy
              exact Or.inl hy
            exact hsubset hx_int
        | inr hxU =>
            -- Case `x` lies in the big union over `s`
            have hx_int : x ∈
                interior (closure (⋃ B ∈ s, (B : Set X))) := h_s hxU
            have hsubset :
                interior (closure (⋃ B ∈ s, (B : Set X))) ⊆
                  interior (closure (A ∪ ⋃ B ∈ s, (B : Set X))) := by
              apply interior_mono
              apply closure_mono
              intro y hy
              exact Or.inr hy
            exact hsubset hx_int
      -- Relate the two ways of writing the union
      have h_eq :
          (⋃ B ∈ (insert A s : Finset (Set X)), (B : Set X)) =
            (A ∪ ⋃ B ∈ s, (B : Set X)) := by
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨B, hx₁⟩
          rcases Set.mem_iUnion.1 hx₁ with ⟨hBmem, hxB⟩
          have h_cases : (B : Set X) = A ∨ (B : Set X) ∈ s :=
            (Finset.mem_insert).1 hBmem
          cases h_cases with
          | inl hBA =>
              left
              simpa [hBA] using hxB
          | inr hBinS =>
              right
              have : x ∈ ⋃ B ∈ s, (B : Set X) := by
                apply Set.mem_iUnion.2
                exact ⟨B, Set.mem_iUnion.2 ⟨hBinS, hxB⟩⟩
              exact this
        · intro hx
          cases hx with
          | inl hxA =>
              apply Set.mem_iUnion.2
              exact ⟨A, Set.mem_iUnion.2
                    ⟨Finset.mem_insert_self _ _, hxA⟩⟩
          | inr hxUnion =>
              rcases Set.mem_iUnion.1 hxUnion with ⟨B, hx₁⟩
              rcases Set.mem_iUnion.1 hx₁ with ⟨hBmem, hxB⟩
              apply Set.mem_iUnion.2
              exact ⟨B, Set.mem_iUnion.2
                    ⟨Finset.mem_insert_of_mem hBmem, hxB⟩⟩
      simpa [h_eq] using h_union

theorem P1_bUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {F : ι → Set X} (s : Finset ι) (hF : ∀ i ∈ s, Topology.P1 (F i)) : Topology.P1 (⋃ i ∈ s, F i) := by
  classical
  revert hF
  induction s using Finset.induction with
  | empty =>
      intro _hF
      simpa using (P1_empty : Topology.P1 (∅ : Set X))
  | @insert i s hi_notin_s ih =>
      intro hF
      -- `P1` for the distinguished index `i`
      have hFi : Topology.P1 (F i) :=
        hF i (Finset.mem_insert_self _ _)
      -- `P1` for the remaining indices, by induction hypothesis
      have hRest : Topology.P1 (⋃ j ∈ s, F j) :=
        ih (by
          intro j hj
          exact hF j (Finset.mem_insert_of_mem hj))
      -- Combine the two using `P1_union`
      have h_union : Topology.P1 (F i ∪ ⋃ j ∈ s, F j) :=
        P1_union hFi hRest
      -- Relate the two ways of writing the union
      have h_eq :
          (⋃ j ∈ (insert i s : Finset ι), F j : Set X) =
            (F i ∪ ⋃ j ∈ s, F j) := by
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨j, hx₁⟩
          rcases Set.mem_iUnion.1 hx₁ with ⟨hjmem, hxj⟩
          have h_cases : j = i ∨ j ∈ s := (Finset.mem_insert).1 hjmem
          cases h_cases with
          | inl hji =>
              left
              simpa [hji] using hxj
          | inr hjs =>
              right
              have : x ∈ ⋃ j ∈ s, F j := by
                apply Set.mem_iUnion.2
                exact ⟨j, Set.mem_iUnion.2 ⟨hjs, hxj⟩⟩
              exact this
        · intro hx
          cases hx with
          | inl hxi =>
              apply Set.mem_iUnion.2
              exact ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_insert_self _ _, hxi⟩⟩
          | inr hxrest =>
              rcases Set.mem_iUnion.1 hxrest with ⟨j, hx₁⟩
              rcases Set.mem_iUnion.1 hx₁ with ⟨hjs, hxj⟩
              apply Set.mem_iUnion.2
              exact ⟨j, Set.mem_iUnion.2 ⟨Finset.mem_insert_of_mem hjs, hxj⟩⟩
      simpa [h_eq] using h_union

theorem P3_exists_dense_Gδ {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A → ∃ G, IsOpen G ∧ (∀ n : ℕ, ∃ U, IsOpen U ∧ closure U ⊆ G) ∧ closure G = closure A := by
  intro hP3
  rcases exists_dense_open_of_P3 (A := A) hP3 with ⟨G, hG_open, hG_closure⟩
  refine ⟨G, hG_open, ?_, hG_closure⟩
  intro n
  refine ⟨(∅ : Set X), isOpen_empty, ?_⟩
  simp

theorem P2_sdiff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : IsClosed B) : Topology.P2 (A \ B) := by
  intro x hx
  -- Split the membership information.
  have hxA : x ∈ A := hx.1
  have hx_notB : x ∈ (Bᶜ : Set X) := by
    simpa using hx.2
  -- `P2 A` yields this interior membership.
  have hxU : x ∈ interior (closure (interior A)) := hA hxA
  -- Define the auxiliary open neighbourhood
  have hU_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  have hV_open :
      IsOpen (interior (closure (interior A)) ∩ (Bᶜ : Set X)) :=
    hU_open.inter hB.isOpen_compl
  have hxV :
      x ∈ (interior (closure (interior A)) ∩ (Bᶜ : Set X)) := by
    exact And.intro hxU hx_notB
  -- Show that this neighbourhood is contained in the desired closure.
  have hV_subset :
      (interior (closure (interior A)) ∩ (Bᶜ : Set X) : Set X) ⊆
        closure (interior (A \ B)) := by
    intro y hyV
    -- Extract the facts about `y`.
    have hyU : y ∈ interior (closure (interior A)) := hyV.1
    have hy_notB : y ∈ (Bᶜ : Set X) := hyV.2
    -- Hence `y ∈ closure (interior A)`.
    have hy_cl :
        y ∈ closure (interior A) := by
      have h_sub :
          (interior (closure (interior A)) : Set X) ⊆
            closure (interior A) := interior_subset
      exact h_sub hyU
    -- Prove that `y` belongs to `closure (interior (A \ B))`.
    have : y ∈ closure (interior (A \ B)) := by
      -- Use the neighbourhood formulation of the closure.
      apply (mem_closure_iff).2
      intro W hW_open hyW
      -- Remove the portion inside `B`.
      have hW'_open : IsOpen (W ∩ (Bᶜ : Set X)) :=
        hW_open.inter hB.isOpen_compl
      have hyW' : y ∈ W ∩ (Bᶜ : Set X) := And.intro hyW hy_notB
      -- Since `y ∈ closure (interior A)`, obtain a point of
      -- `interior A` in this neighbourhood.
      rcases
          (mem_closure_iff).1 hy_cl _ hW'_open hyW' with
        ⟨z, hzW', hz_intA⟩
      -- Split the obtained information.
      have hzW : z ∈ W := hzW'.1
      have hz_notB : z ∈ (Bᶜ : Set X) := hzW'.2
      -- We claim that `z ∈ interior (A \ B)`.
      have hz_int_diff : z ∈ interior (A \ B) := by
        -- The open set `interior A ∩ Bᶜ` is contained in `A \ B`.
        have h_basic :
            (interior A ∩ (Bᶜ : Set X) : Set X) ⊆ (A \ B) := by
          intro t ht
          exact And.intro (interior_subset ht.1) ht.2
        have h_open :
            IsOpen (interior A ∩ (Bᶜ : Set X) : Set X) :=
          (isOpen_interior.inter hB.isOpen_compl)
        have h_sub :
            (interior A ∩ (Bᶜ : Set X) : Set X) ⊆
              interior (A \ B) :=
          interior_maximal h_basic h_open
        have hz_mem : z ∈ (interior A ∩ (Bᶜ : Set X) : Set X) :=
          And.intro hz_intA hz_notB
        exact h_sub hz_mem
      -- Provide the desired witness.
      exact ⟨z, And.intro hzW hz_int_diff⟩
    exact this
  -- The neighbourhood is open, hence contained in the interior of the closure.
  have hV_subset_int :
      (interior (closure (interior A)) ∩ (Bᶜ : Set X) : Set X) ⊆
        interior (closure (interior (A \ B))) :=
    interior_maximal hV_subset hV_open
  -- Conclude for the original point `x`.
  exact hV_subset_int hxV