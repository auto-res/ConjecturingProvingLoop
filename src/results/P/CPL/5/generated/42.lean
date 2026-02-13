

theorem P3_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : IsClosed B) : P3 (A \ B) := by
  intro x hx
  -- `hx` gives membership in `A` and not in `B`.
  have hxA : x ∈ A := hx.1
  have hxNotB : x ∈ (Bᶜ) := hx.2
  -- `hA` yields interior membership w.r.t. `closure A`.
  have hx_int : x ∈ interior (closure A) := hA hxA
  -- Define the auxiliary open neighbourhood
  let U : Set X := interior (closure A) ∩ Bᶜ
  have hU_open : IsOpen U := by
    dsimp [U]
    exact (isOpen_interior).inter hB.isOpen_compl
  -- Show that `U ⊆ closure (A \ B)`.
  have hU_subset : (U : Set X) ⊆ closure (A \ B) := by
    intro y hyU
    -- Decompose the membership information.
    have hy_int : y ∈ interior (closure A) := hyU.1
    have hyNotB : y ∈ (Bᶜ) := hyU.2
    -- From interior to closure.
    have hy_clA : y ∈ closure A := interior_subset hy_int
    -- Use the neighbourhood characterization of closure.
    have : y ∈ closure (A \ B) := by
      apply (mem_closure_iff).2
      intro V hV_open hyV
      -- Refine the neighbourhood so that it avoids `B`.
      have hW_open : IsOpen (V ∩ Bᶜ) := hV_open.inter hB.isOpen_compl
      have hyW : y ∈ V ∩ Bᶜ := ⟨hyV, hyNotB⟩
      -- Since `y ∈ closure A`, this refined neighbourhood meets `A`.
      rcases (mem_closure_iff).1 hy_clA (V ∩ Bᶜ) hW_open hyW with ⟨z, hzW, hzA⟩
      -- Extract the required witness in `A \ B`.
      have hzV : z ∈ V := hzW.1
      have hzNotB : z ∈ (Bᶜ) := hzW.2
      exact ⟨z, ⟨hzV, ⟨hzA, hzNotB⟩⟩⟩
    exact this
  -- `x` certainly belongs to `U`.
  have hxU : x ∈ U := by
    dsimp [U]
    exact ⟨hx_int, hxNotB⟩
  -- Maximality of the interior gives the desired membership.
  have hU_to_int : (U : Set X) ⊆ interior (closure (A \ B)) :=
    interior_maximal hU_subset hU_open
  exact hU_to_int hxU