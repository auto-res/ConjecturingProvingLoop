

theorem Topology.boundary_subset_interior_closure_iff_P3_of_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    (closure (A : Set X) \ interior A ⊆ interior (closure A)) ↔
      Topology.P3 (X := X) A := by
  -- `A` is closed, so `closure A = A`.
  have h_cl : closure (A : Set X) = A := hA_closed.closure_eq
  have h_int_cl : interior (closure (A : Set X)) = interior A := by
    simpa [h_cl]
  ------------------------------------------------------------------
  --  Step 1: translate the boundary–interior inclusion into
  --          the openness of `A`.
  ------------------------------------------------------------------
  have h_equiv_open :
      (closure (A : Set X) \ interior A ⊆ interior (closure A)) ↔
        IsOpen (A : Set X) := by
    -- First, rewrite the inclusion entirely in terms of `A`.
    have h_rewrite :
        (closure (A : Set X) \ interior A ⊆ interior (closure A)) ↔
          (A \ interior A ⊆ interior A) := by
      simpa [h_cl, h_int_cl]
    -- Next, characterize the resulting inclusion.
    have h_aux :
        (A \ interior A ⊆ interior A) ↔ IsOpen (A : Set X) := by
      constructor
      · intro h_subset
        -- Show `interior A = A`, hence `A` is open.
        have h_eq : interior (A : Set X) = A := by
          apply Set.Subset.antisymm
          · exact interior_subset
          · intro x hxA
            by_cases hx_int : (x : X) ∈ interior A
            · exact hx_int
            ·
              have hx_boundary : (x : X) ∈ A \ interior A := ⟨hxA, hx_int⟩
              exact h_subset hx_boundary
        simpa [h_eq] using (isOpen_interior : IsOpen (interior (A : Set X)))
      · intro h_open
        -- If `A` is open, the boundary `A \ interior A` is empty,
        -- so the inclusion holds trivially.
        have h_int_eq : interior (A : Set X) = A := h_open.interior_eq
        have : (A \ interior A : Set X) = ∅ := by
          simpa [h_int_eq, Set.diff_self]
        simpa [this]
    exact h_rewrite.trans h_aux
  ------------------------------------------------------------------
  --  Step 2: invoke the closed–set equivalence `P3 ↔ isOpen`.
  ------------------------------------------------------------------
  have h_equiv_P3 :
      IsOpen (A : Set X) ↔ Topology.P3 (X := X) A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed).symm
  ------------------------------------------------------------------
  --  Step 3: put the pieces together.
  ------------------------------------------------------------------
  simpa using h_equiv_open.trans h_equiv_P3