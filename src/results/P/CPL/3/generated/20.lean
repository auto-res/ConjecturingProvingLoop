

theorem P3_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 (Set.prod A B) → P3 (Set.prod B A) := by
  intro hP3
  -- We must show: every point of `B ×ˢ A` lies in the interior of the closure
  -- of `B ×ˢ A`.
  intro p hp
  ----------------------------------------------------------------
  -- 1.  Apply `hP3` to the swapped point `p.swap : X × Y`.
  ----------------------------------------------------------------
  have hp_swap_mem : Prod.swap p ∈ Set.prod A B := by
    rcases hp with ⟨hpB, hpA⟩
    exact ⟨hpA, hpB⟩
  have h_int_swap : Prod.swap p ∈ interior (closure (Set.prod A B)) :=
    hP3 hp_swap_mem
  ----------------------------------------------------------------
  -- 2.  Define auxiliary sets `U` and `V`.
  ----------------------------------------------------------------
  let U : Set (X × Y) := interior (closure (Set.prod A B))
  have hU_open : IsOpen U := by
    dsimp [U]
    exact isOpen_interior
  let V : Set (Y × X) := Prod.swap ⁻¹' U
  ----------------------------------------------------------------
  -- 3.  `V` is open since `Prod.swap` is a homeomorphism.
  ----------------------------------------------------------------
  have h_cont_swap : Continuous (Prod.swap : (Y × X) → (X × Y)) :=
    (Homeomorph.prodComm Y X).continuous_toFun
  have hV_open : IsOpen V := by
    dsimp [V]
    exact h_cont_swap.isOpen_preimage (s := U) hU_open
  ----------------------------------------------------------------
  -- 4.  Our point `p` belongs to `V`.
  ----------------------------------------------------------------
  have hpV : p ∈ V := by
    dsimp [V] at *
    exact h_int_swap
  ----------------------------------------------------------------
  -- 5.  Show that `V ⊆ closure (B ×ˢ A)`.
  ----------------------------------------------------------------
  have hV_sub_closure : V ⊆ closure (Set.prod B A) := by
    intro x hxV
    -- First, get that `x.swap` lies in the closure of `A ×ˢ B`.
    have hxU : Prod.swap x ∈ U := by
      simpa [V] using hxV
    have h_swap_x_cl : Prod.swap x ∈ closure (Set.prod A B) := by
      dsimp [U] at hxU
      exact interior_subset hxU
    -- Rewrite `closure (A ×ˢ B)` as a product of closures.
    have hset1 : closure (Set.prod A B) = closure A ×ˢ closure B := by
      simpa using closure_prod_eq
    have h_coords : Prod.swap x ∈ closure A ×ˢ closure B := by
      simpa [hset1] using h_swap_x_cl
    rcases h_coords with ⟨hxA_cl, hxB_cl⟩
    -- Swap the coordinates back.
    have hx_prod : x ∈ closure B ×ˢ closure A := ⟨hxB_cl, hxA_cl⟩
    -- Turn this into the required membership.
    have hset2 : closure (Set.prod B A) = closure B ×ˢ closure A := by
      simpa using closure_prod_eq
    simpa [hset2] using hx_prod
  ----------------------------------------------------------------
  -- 6.  Since `V` is open, it is contained in the desired interior.
  ----------------------------------------------------------------
  have hV_sub_interior :
      V ⊆ interior (closure (Set.prod B A)) :=
    interior_maximal hV_sub_closure hV_open
  ----------------------------------------------------------------
  -- 7.  Conclude for the original point `p`.
  ----------------------------------------------------------------
  exact hV_sub_interior hpV