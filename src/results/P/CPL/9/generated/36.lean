

theorem P2_of_P1 {A : Set X} (h : P1 A) (h_open_cl : IsOpen (closure A)) : P2 A := by
  intro x hxA
  -- `x` lies in `closure A`
  have hx_closureA : (x : X) ∈ closure A := subset_closure hxA
  -- `closure A ⊆ closure (interior A)` since `A ⊆ closure (interior A)`
  have h_subset : (closure A : Set X) ⊆ closure (interior A) := by
    have hA_subset : (A : Set X) ⊆ closure (interior A) := h
    simpa using (closure_mono hA_subset)
  -- An open set contained in a set is contained in its interior
  have h_closure_in_int :
      (closure A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal h_subset h_open_cl
  exact h_closure_in_int hx_closureA

theorem P3_subset_closure {A : Set X} (hA : P3 A) : interior A ⊆ interior (closure A) := by
  intro x hx
  exact hA (interior_subset hx)

theorem P1_of_open {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact subset_closure hx_int