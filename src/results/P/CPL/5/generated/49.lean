

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : IsClosed B) : P2 (A \ B) := by
  intro x hx
  -- `hx` gives the two components of membership.
  have hx_int : x ∈ interior (closure (interior A)) := by
    exact hA hx.1
  -- Define an auxiliary open neighbourhood that avoids `B`.
  let U : Set X := interior (closure (interior A)) ∩ Bᶜ
  have hU_open : IsOpen U := by
    dsimp [U]
    exact isOpen_interior.inter hB.isOpen_compl
  -- Show that this neighbourhood is contained in the desired closure.
  have hU_subset : (U : Set X) ⊆ closure (interior (A \ B)) := by
    intro y hyU
    -- Decompose the membership information.
    have hy_int : y ∈ interior (closure (interior A)) := hyU.1
    have hy_notB : y ∈ Bᶜ := hyU.2
    have hy_cl : y ∈ closure (interior A) := interior_subset hy_int
    -- Use the neighbourhood characterisation of the closure.
    have : y ∈ closure (interior (A \ B)) := by
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- Refine the neighbourhood so that it avoids `B`.
      have hW_open : IsOpen (V ∩ Bᶜ) := hVopen.inter hB.isOpen_compl
      have hyW : y ∈ V ∩ Bᶜ := ⟨hyV, hy_notB⟩
      -- Because `y ∈ closure (interior A)`, this refined neighbourhood meets `interior A`.
      have h_non : ((V ∩ Bᶜ) ∩ interior A).Nonempty := by
        have := (mem_closure_iff).1 hy_cl (V ∩ Bᶜ) hW_open hyW
        simpa [Set.inter_assoc, Set.inter_left_comm] using this
      rcases h_non with ⟨z, ⟨⟨hzV, hzNotB⟩, hzIntA⟩⟩
      -- `z` is in `interior A` and avoids `B`; show it is in `interior (A \ B)`.
      have hz_int_diff : z ∈ interior (A \ B) := by
        -- The open set `interior A ∩ Bᶜ` is contained in `A \ B`.
        have hOpen : IsOpen (interior A ∩ Bᶜ) :=
          isOpen_interior.inter hB.isOpen_compl
        have hSub : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
          intro w hw
          exact ⟨(interior_subset : interior A ⊆ A) hw.1, hw.2⟩
        have hzU : z ∈ interior A ∩ Bᶜ := ⟨hzIntA, hzNotB⟩
        exact (mem_interior.2 ⟨_, hSub, hOpen, hzU⟩)
      -- Provide the witness in `V ∩ interior (A \ B)`.
      exact ⟨z, hzV, hz_int_diff⟩
    exact this
  -- The point `x` lies in `U`.
  have hxU : x ∈ U := by
    dsimp [U]
    exact ⟨hx_int, hx.2⟩
  -- Maximality of the interior yields the desired membership.
  have h_in : x ∈ interior (closure (interior (A \ B))) :=
    (interior_maximal hU_subset hU_open) hxU
  exact h_in

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P3 A := by
  exact P3_of_P2 (A := A) (P2_of_dense_interior (A := A) h)