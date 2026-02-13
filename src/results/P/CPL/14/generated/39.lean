

theorem P3_interior_closure {X} [TopologicalSpace X] {A : Set X} : P3 (interior (closure A)) := by
  simpa using (P3_of_open (A := interior (closure A)) isOpen_interior)

theorem P1_iff_P2_of_boundary_empty {X} [TopologicalSpace X] {A : Set X} (h : frontier A = ∅) : P1 A ↔ P2 A := by
  -- First, prove `closure A ⊆ interior A` from `frontier A = ∅`.
  have h_subset : (closure (A : Set X)) ⊆ interior A := by
    intro x hx_cl
    by_cases hx_int : x ∈ interior A
    · exact hx_int
    · -- Otherwise `x` would lie in the (empty) frontier – contradiction.
      have hx_frontier : x ∈ frontier A := by
        -- `frontier A = closure A \ interior A`
        exact And.intro hx_cl hx_int
      have h_not_mem : x ∉ frontier A := by
        -- No point lies in an empty set.
        have h_forall := (Set.eq_empty_iff_forall_not_mem).1 h
        exact h_forall x
      exact False.elim (h_not_mem hx_frontier)
  ----------------------------------------------------------------
  -- From the two inclusions we deduce `interior A = A`, hence `A` is open.
  ----------------------------------------------------------------
  have h_int_eq : (interior A : Set X) = A := by
    apply Set.Subset.antisymm
    · exact interior_subset
    · intro x hxA
      have : x ∈ closure (A : Set X) := subset_closure hxA
      exact h_subset this
  have hA_open : IsOpen A := by
    have : IsOpen (interior A) := isOpen_interior
    simpa [h_int_eq] using this
  ----------------------------------------------------------------
  -- For open sets `P1` and `P2` coincide.
  ----------------------------------------------------------------
  simpa using (P1_iff_P2_of_open (A := A) hA_open)