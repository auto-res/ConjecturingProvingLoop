

theorem interior_closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  -- Let `S = interior (closure A)`.
  set S : Set X := interior (closure A) with hS_def
  -- `closure S` is contained in `closure A`.
  have h_closure_subset : closure S ⊆ closure A := by
    -- Since `S ⊆ closure A`, taking closures yields the inclusion.
    have hS_subset : S ⊆ closure A := by
      dsimp [S] at *
      exact interior_subset
    simpa [closure_closure, hS_def] using closure_mono hS_subset
  -- Hence `interior (closure S) ⊆ S`.
  have h_int_subset : interior (closure S) ⊆ S := by
    have h := interior_mono h_closure_subset
    simpa [hS_def] using h
  -- Because `S` is open, we also have `S ⊆ interior (closure S)`.
  have h_subset_int : S ⊆ interior (closure S) := by
    intro x hxS
    -- `S` is open, so `interior S = S`.
    have h_open : IsOpen S := by
      dsimp [S] at *
      exact isOpen_interior
    have hx_int_S : x ∈ interior S := by
      simpa [h_open.interior_eq] using hxS
    -- Monotonicity of `interior`.
    have h_int_mono : interior S ⊆ interior (closure S) :=
      interior_mono subset_closure
    exact h_int_mono hx_int_S
  -- Combine the inclusions to obtain equality.
  have h_eq : interior (closure S) = S :=
    subset_antisymm h_int_subset h_subset_int
  simpa [hS_def] using h_eq