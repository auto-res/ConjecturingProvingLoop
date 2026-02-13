

theorem P1_from_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P1 (closure A) := by
  intro x hx_cl
  -- Step 1: use `hA : P2 A` to reach the intermediate closure
  have hx₁ : x ∈ closure (interior (closure (interior A))) := by
    have h_subset : (closure A : Set X) ⊆ closure (interior (closure (interior A))) :=
      closure_mono (hA : (A : Set X) ⊆ interior (closure (interior A)))
    exact h_subset hx_cl
  -- Step 2: compare the two target closures
  have h_subset' :
      (closure (interior (closure (interior A))) : Set X) ⊆
        closure (interior (closure A)) := by
    have h_inner :
        (interior (closure (interior A)) : Set X) ⊆ interior (closure A) := by
      have h_cl :
          (closure (interior A) : Set X) ⊆ closure A :=
        closure_mono (interior_subset : (interior A : Set X) ⊆ A)
      exact interior_mono h_cl
    exact closure_mono h_inner
  exact h_subset' hx₁

theorem closure_eq_iterated_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : closure A = closure (interior (closure (interior A))) := by
  -- Step 1: `closure A = closure (interior A)` from `P1`.
  have h₁ : closure (A : Set X) = closure (interior A) :=
    closure_eq_of_P1 (A := A) hA
  -- Step 2: `closure (interior A)` equals the required iterated closure.
  have h₂ : closure (interior A) = closure (interior (closure (interior A))) := by
    -- `interior A` satisfies `P2`.
    have hP2 : P2 (interior A) := P2_interior (A := A)
    -- Use the equality given by `P2`, reversing its orientation.
    simpa using
      (closure_eq_interior_closure_of_P2 (A := interior A) hP2).symm
  -- Combine the two equalities.
  simpa using h₁.trans h₂