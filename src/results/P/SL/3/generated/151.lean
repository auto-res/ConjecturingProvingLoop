

theorem interior_inter_eq_of_isOpen_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) :
    interior (A ∩ B : Set X) = A ∩ interior (B : Set X) := by
  apply Set.Subset.antisymm
  · -- `interior (A ∩ B) ⊆ A ∩ interior B`
    intro x hx
    have hAB : (x : X) ∈ (A ∩ B : Set X) := interior_subset hx
    have hA_mem : (x : X) ∈ A := hAB.1
    -- Monotonicity of `interior`
    have h_intB : (x : X) ∈ interior (B : Set X) := by
      have h_subset : (A ∩ B : Set X) ⊆ (B : Set X) := Set.inter_subset_right
      exact (interior_mono h_subset) hx
    exact And.intro hA_mem h_intB
  · -- `A ∩ interior B ⊆ interior (A ∩ B)`
    intro x hx
    rcases hx with ⟨hA_mem, h_intB⟩
    -- The open set `A ∩ interior B` contains `x` and lies inside `A ∩ B`
    have h_open : IsOpen (A ∩ interior (B : Set X)) := hA.inter isOpen_interior
    have hx_open : (x : X) ∈ (A ∩ interior (B : Set X)) :=
      And.intro hA_mem h_intB
    have hx_int_open : (x : X) ∈ interior (A ∩ interior (B : Set X)) := by
      simpa [h_open.interior_eq] using hx_open
    have h_subset : (A ∩ interior (B : Set X)) ⊆ A ∩ B := by
      intro y hy
      exact And.intro hy.1 (interior_subset hy.2)
    exact (interior_mono h_subset) hx_int_open