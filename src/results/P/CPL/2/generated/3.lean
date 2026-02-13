

theorem P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : P1 (X:=X) A) (h3 : P3 (X:=X) A) : P2 A := by
  -- Obtain equality of closures from `P1`
  have h_cl : closure A = closure (interior A) :=
    ((P1_iff_closure_interior_subset).1 h1).symm
  -- Unfold `P2` and prove the required inclusion
  unfold P2
  intro x hx
  -- Apply `P3` and rewrite using the closure equality
  have hx' : x ∈ interior (closure A) := h3 hx
  simpa [h_cl] using hx'

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 (X:=X) A := by
  -- Unfold the definition of `P2`
  unfold P2
  intro x hx
  -- An open set is contained in the interior of its closure
  have h_subset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  have hx' : x ∈ interior (closure A) := h_subset hx
  -- Since `interior A = A`, rewrite the goal accordingly
  simpa [hA.interior_eq] using hx'

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 (X:=X) A := by
  -- Unfold the definition of `P3`
  unfold P3
  -- We must show `A ⊆ interior (closure A)`
  intro x hx
  -- Since `A` is open, `interior A = A`
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  -- From `A ⊆ closure A`, deduce `interior A ⊆ interior (closure A)`
  have h_subset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact h_subset hx_int