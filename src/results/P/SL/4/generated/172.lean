

theorem closure_compl_eq_compl_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (Aᶜ) = (interior A)ᶜ := by
  -- Apply `interior_compl_eq_compl_closure` to `Aᶜ`:
  have h : interior A = (closure (Aᶜ))ᶜ := by
    have h' := interior_compl_eq_compl_closure (X := X) (A := Aᶜ)
    simpa [compl_compl] using h'
  -- Complement both sides of `h` to obtain the desired equality.
  have h' : (interior A)ᶜ = closure (Aᶜ) := by
    simpa using congrArg Set.compl h
  simpa using h'.symm