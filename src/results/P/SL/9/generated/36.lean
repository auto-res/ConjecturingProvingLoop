

theorem interior_closure_interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  -- Let `S = interior (closure (interior A))`.
  set S : Set X := interior (closure (interior A)) with hS_def
  -- We first show that `closure S ⊆ closure (interior A)`.
  have h_closure_subset : closure S ⊆ closure (interior A) := by
    -- Since `S ⊆ closure (interior A)`, taking closures yields the claim.
    have h_S_subset : S ⊆ closure (interior A) := by
      dsimp [S] at *
      exact interior_subset
    simpa [closure_closure] using closure_mono h_S_subset
  -- From the previous inclusion we get `interior (closure S) ⊆ S`.
  have h_int_subset : interior (closure S) ⊆ S := by
    have h := interior_mono h_closure_subset
    simpa [hS_def] using h
  -- Because `S` is open and `S ⊆ closure S`, we have `S ⊆ interior (closure S)`.
  have h_subset_int : S ⊆ interior (closure S) := by
    have h_open : IsOpen S := by
      dsimp [S]; exact isOpen_interior
    have h_sub : S ⊆ closure S := subset_closure
    exact interior_maximal h_sub h_open
  -- Combine the two inclusions to obtain equality.
  have h_eq : interior (closure S) = S := subset_antisymm h_int_subset h_subset_int
  simpa [hS_def] using h_eq