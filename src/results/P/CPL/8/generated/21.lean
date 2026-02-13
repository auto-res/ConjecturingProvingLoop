

theorem P3_sigma {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {A : ∀ i, Set (X i)} : (∀ i, P3 (A i)) → P3 {p : Σ i, X i | P3 (A p.1)} := by
  intro hAll
  -- The set in question is actually the whole space.
  have h_eq :
      ({p : Sigma X | P3 (A p.1)} : Set (Sigma X)) = Set.univ := by
    ext p
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact hAll p.1
  -- `P3` holds for `Set.univ`, hence for our set.
  simpa [h_eq.symm] using (P3_univ (X := Sigma X))

theorem P1_sigma {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {A : ∀ i, Set (X i)} : (∀ i, P1 (A i)) → P1 {p : Σ i, X i | P1 (A p.1)} := by
  intro hAll
  have h_eq :
      ({p : Sigma X | P1 (A p.1)} : Set (Sigma X)) = Set.univ := by
    ext p
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact hAll p.1
  simpa [h_eq.symm] using (P1_univ (X := Sigma X))