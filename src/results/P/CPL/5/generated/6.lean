

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : P2 A := by
  intro x hx
  -- First, show that `A` must be the whole space.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; simp
    · intro _
      have h_eq : y = x := Subsingleton.elim _ _
      simpa [h_eq] using hx
  -- Now the claim follows by rewriting with `hA_univ`.
  simpa [hA_univ, interior_univ, closure_univ]