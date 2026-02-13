

theorem P3_inter_open_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 A) (hOpenB : IsOpen (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  -- Unfold the definition of `P3`.
  dsimp [Topology.P3] at hP3A ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P3` for `A`, obtain that `x` lies in `interior (closure A)`.
  have hxIntA : x ∈ interior (closure A) := hP3A hxA
  -- Consider the open set `W = interior (closure A) ∩ B`.
  let W : Set X := interior (closure A) ∩ B
  have hW_open : IsOpen W :=
    isOpen_interior.inter hOpenB
  have hxW : x ∈ W := by
    exact And.intro hxIntA hxB
  -- We show that `W` is contained in `closure (A ∩ B)`.
  have hW_sub_cl : (W : Set X) ⊆ closure (A ∩ B) := by
    intro y hy
    rcases hy with ⟨hyIntA, hyB⟩
    -- `y ∈ interior (closure A)` implies `y ∈ closure A`.
    have hyClA : y ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hyIntA
    -- Use the neighbourhood characterisation of the closure.
    have : y ∈ closure (A ∩ B) := by
      -- Reformulate `hyClA` via `mem_closure_iff`.
      have hClosureA :=
        (mem_closure_iff).1 hyClA
      -- Show that every open neighbourhood of `y` meets `A ∩ B`.
      have hClosureAB : ∀ U : Set X, IsOpen U → y ∈ U →
          (U ∩ (A ∩ B) : Set X).Nonempty := by
        intro U hU_open hyU
        -- Intersect the neighbourhood with `B`, which is open.
        have hV_open : IsOpen (U ∩ B) := hU_open.inter hOpenB
        have hyV : y ∈ U ∩ B := ⟨hyU, hyB⟩
        -- `U ∩ B` meets `A` since `y ∈ closure A`.
        have hNonempty : ((U ∩ B) ∩ A).Nonempty :=
          hClosureA (U ∩ B) hV_open hyV
        rcases hNonempty with ⟨z, ⟨⟨hzU, hzB⟩, hzA⟩⟩
        -- The point `z` lies in `U ∩ (A ∩ B)`.
        exact ⟨z, ⟨hzU, ⟨hzA, hzB⟩⟩⟩
      -- Translate the neighbourhood property back into membership in the closure.
      exact (mem_closure_iff).2 hClosureAB
    exact this
  -- By maximality of the interior, `W ⊆ interior (closure (A ∩ B))`.
  have hW_sub_int :
      (W : Set X) ⊆ interior (closure (A ∩ B)) :=
    interior_maximal hW_sub_cl hW_open
  -- Conclude by applying the inclusion to `x`.
  exact hW_sub_int hxW