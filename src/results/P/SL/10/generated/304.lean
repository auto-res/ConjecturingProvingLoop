

theorem Topology.interior_diff_open_left_eq_inter_interior_compl
    {X : Type*} [TopologicalSpace X] {U A : Set X} (hU : IsOpen U) :
    interior (U \ A) = U ∩ interior (Aᶜ) := by
  -- Step 1: rewrite `interior (U \ A)` using an existing lemma.
  have h₁ :=
    Topology.interior_diff_eq_diff_closure_of_isOpen
      (X := X) (A := U) (B := A) hU
  -- Step 2: express `interior (Aᶜ)` in terms of `closure A`.
  have h_int_compl :
      interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  -- Step 3: chain the equalities to reach the desired identity.
  calc
    interior (U \ A)
        = U \ closure A := h₁
    _ = U ∩ (closure A)ᶜ := by
        simp [Set.diff_eq]
    _ = U ∩ interior (Aᶜ) := by
        simpa [h_int_compl]