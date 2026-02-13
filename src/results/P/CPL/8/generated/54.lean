

theorem P3_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} : A = ∅ → (P3 A ↔ True) := by
  intro hA
  have hP3 : P3 A := by
    simpa [hA] using (P3_empty (X := X))
  simpa using (iff_true_intro hP3)

theorem P1_Union₂ {X : Type*} [TopologicalSpace X] {ι κ : Sort*} {A : ι → κ → Set X} : (∀ i j, P1 (A i j)) → P1 (⋃ i, ⋃ j, A i j) := by
  intro hAll
  -- First, establish `P1` for `⋃ j, A i j` for each fixed `i`.
  have hP1_i : ∀ i, P1 (⋃ j, A i j) := by
    intro i
    have hP1_ij : ∀ j, P1 (A i j) := fun j => hAll i j
    simpa using (P1_unionᵢ (A := fun j => A i j) hP1_ij)
  -- Then, use `P1_unionᵢ` once more to get the result for the double union.
  simpa using (P1_unionᵢ (A := fun i => ⋃ j, A i j) hP1_i)

theorem P3_sigma_swap {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {A : ∀ i, Set (X i)} : (∀ i, P3 (A i)) → P3 {p : Σ i, X i | P3 (A p.1) ∧ True} := by
  intro hAll
  -- Show the defining set is the whole space.
  have h_eq :
      ({p : Sigma X | P3 (A p.1) ∧ True} : Set (Sigma X)) = Set.univ := by
    ext p
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact And.intro (hAll p.1) trivial
  -- Conclude using `P3_univ`.
  simpa [h_eq.symm] using (P3_univ (X := Sigma X))