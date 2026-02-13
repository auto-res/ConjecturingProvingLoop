

theorem P3_sdiff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : IsClosed B) : Topology.P3 (A \ B) := by
  intro x hx
  -- Split the membership information.
  have hxA : x ∈ A := hx.1
  have hx_notB : x ∈ (Bᶜ : Set X) := by
    simpa using hx.2
  -- From `P3 A`, `x` lies in the interior of the closure of `A`.
  have hx_int : x ∈ interior (closure (A : Set X)) := hA hxA
  -- Define `U := interior (closure A)`.
  let U : Set X := interior (closure (A : Set X))
  have hU_open : IsOpen U := isOpen_interior
  have hxU : x ∈ U := by
    dsimp [U] at *
    exact hx_int
  -- Define `V := U ∩ Bᶜ`, an open neighbourhood of `x`.
  let V : Set X := U ∩ (Bᶜ : Set X)
  have hV_open : IsOpen V := hU_open.inter hB.isOpen_compl
  have hxV : x ∈ V := by
    dsimp [V] at *
    exact And.intro hxU hx_notB
  -- Show `V ⊆ closure (A \ B)`.
  have hV_subset : (V : Set X) ⊆ closure (A \ B) := by
    intro y hyV
    have hyU : y ∈ U := hyV.1
    have hy_notB : y ∈ (Bᶜ : Set X) := hyV.2
    -- `y` belongs to `closure A`.
    have hy_clA : y ∈ closure (A : Set X) := by
      have : (U : Set X) ⊆ closure A := interior_subset
      exact this hyU
    -- Use the neighbourhood criterion for the closure.
    have : y ∈ closure (A \ B) := by
      apply (mem_closure_iff).2
      intro W hW_open hyW
      -- Shrink the neighbourhood inside `Bᶜ`.
      have hW'_open : IsOpen (W ∩ (Bᶜ : Set X)) :=
        hW_open.inter hB.isOpen_compl
      have hyW' : y ∈ W ∩ (Bᶜ : Set X) := And.intro hyW hy_notB
      -- Since `y ∈ closure A`, this set meets `A`.
      rcases
          (mem_closure_iff).1 hy_clA _ hW'_open hyW' with
        ⟨z, hzW', hzA⟩
      have hzW : z ∈ W := hzW'.1
      have hz_notB : z ∈ (Bᶜ : Set X) := hzW'.2
      have hz_diff : z ∈ A \ B := And.intro hzA hz_notB
      exact ⟨z, And.intro hzW hz_diff⟩
    exact this
  -- `V` is open and contained in the desired closure, hence in its interior.
  have hV_subset_int :
      (V : Set X) ⊆ interior (closure (A \ B)) :=
    interior_maximal hV_subset hV_open
  -- Conclude that `x` lies in the required interior.
  exact hV_subset_int hxV