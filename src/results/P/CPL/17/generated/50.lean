

theorem P3_of_closure_is_open {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsOpen (closure A)) : Topology.P3 A := by
  intro x hxA
  have hx_cl : (x : X) ∈ closure A := subset_closure hxA
  simpa [h.interior_eq] using hx_cl

theorem P2_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P3 A → Topology.P2 A := by
  intro hA_closed hP3
  simpa using ((P3_iff_P2_for_closed (A := A) hA_closed).1 hP3)

theorem P3_of_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} : A ⊆ B → Dense A → Topology.P3 B := by
  intro hAB hDense
  -- The closure of `A` is the whole space.
  have hClA : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence the closure of `B` is also the whole space.
  have hClB : closure (B : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _
      simp
    ·
      have : closure (A : Set X) ⊆ closure B := closure_mono hAB
      simpa [hClA] using this
  -- Conclude using the lemma `P3_of_closure_eq_univ`.
  exact (P3_of_closure_eq_univ (A := B)) hClB

theorem P2_intersection_open {X : Type*} [TopologicalSpace X] {A U : Set X} : IsOpen U → Topology.P2 A → Topology.P2 (A ∩ U) := by
  intro hU_open hP2A
  intro x hxAU
  -- Split the hypothesis `x ∈ A ∩ U`
  have hxA : x ∈ A := hxAU.1
  have hxU : x ∈ U := hxAU.2
  -- Apply `P2` for `A`
  have hxIntCl : x ∈ interior (closure (interior A)) := hP2A hxA
  -- We will show that
  --   interior (closure (interior A)) ∩ U ⊆
  --   interior (closure (interior (A ∩ U))).
  -- This will give the result because `x` lies in the left–hand set.
  have h_subset :
      (interior (closure (interior A)) ∩ U : Set X) ⊆
        interior (closure (interior (A ∩ U))) := by
    -- The set on the left is open.
    have h_open :
        IsOpen (interior (closure (interior A)) ∩ U) :=
      (isOpen_interior).inter hU_open
    -- Show that it is contained in the closure on the right.
    have h_sub_closure :
        (interior (closure (interior A)) ∩ U : Set X) ⊆
          closure (interior (A ∩ U)) := by
      intro y hy
      -- `y` is in both components of the intersection
      have hyIntCl : y ∈ interior (closure (interior A)) := hy.1
      have hyU     : y ∈ U := hy.2
      -- Hence `y` is also in `closure (interior A)`.
      have hyCl : y ∈ closure (interior A) :=
        (interior_subset :
            interior (closure (interior A)) ⊆ closure (interior A)) hyIntCl
      -- Prove that `y` is in `closure (interior (A ∩ U))`
      have : y ∈ closure (interior (A ∩ U)) := by
        -- Use the neighbourhood criterion for closure.
        refine (mem_closure_iff).2 ?_
        intro V hV_open hyV
        -- Work inside the open set `V ∩ U`.
        have hVU_open : IsOpen (V ∩ U) := hV_open.inter hU_open
        have hyVU : y ∈ V ∩ U := ⟨hyV, hyU⟩
        -- Because `y ∈ closure (interior A)`, this set meets `interior A`.
        have h_nonempty :=
          ((mem_closure_iff).1 hyCl) (V ∩ U) hVU_open hyVU
        rcases h_nonempty with ⟨z, hzVU, hzIntA⟩
        -- Split the membership information for `z`.
        have hzV : z ∈ V := hzVU.1
        have hzU : z ∈ U := hzVU.2
        -- Show that `z ∈ interior (A ∩ U)`.
        have hzIntAU : z ∈ interior (A ∩ U) := by
          -- Consider the open set `interior A ∩ U` containing `z`.
          have hK_open : IsOpen (interior A ∩ U) :=
            (isOpen_interior).inter hU_open
          have hzK : z ∈ interior A ∩ U := ⟨hzIntA, hzU⟩
          have hK_sub : (interior A ∩ U : Set X) ⊆ A ∩ U := by
            intro w hw
            exact ⟨
              (interior_subset : interior A ⊆ A) hw.1,
              hw.2⟩
          have hK_int :=
            interior_maximal hK_sub hK_open
          exact hK_int hzK
        -- Produce the required witness for non-emptiness.
        exact ⟨z, ⟨hzV, hzIntAU⟩⟩
      exact this
    -- An open subset of a closure is contained in the corresponding interior.
    exact interior_maximal h_sub_closure h_open
  -- Apply the inclusion to `x`.
  have hx_mem :
      x ∈ (interior (closure (interior A)) ∩ U : Set X) :=
    ⟨hxIntCl, hxU⟩
  exact h_subset hx_mem