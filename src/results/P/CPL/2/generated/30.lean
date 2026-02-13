

theorem exists_set_with_P2 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, Topology.P2 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_⟩
  simpa using (P2_univ (X := X))

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 (X:=X) A := by
  classical
  -- Unfold the definition of `P2`
  unfold Topology.P2
  intro x hxA
  -- Split on whether `A` is empty or not
  by_cases hA : (A : Set X).Nonempty
  · rcases hA with ⟨a, ha⟩
    -- In a subsingleton, any non-empty set is the whole space
    have hAU : (A : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; simp
      · intro _
        have h_eq : y = a := Subsingleton.elim y a
        simpa [h_eq] using ha
    -- The target set is `univ`, so the claim is immediate
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hAU, interior_univ, closure_univ] using this
  · -- If `A` is empty, `x ∈ A` is impossible
    have hContr : (A : Set X).Nonempty := ⟨x, hxA⟩
    exact (hA hContr).elim

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 (X:=X) A := by
  classical
  unfold Topology.P3
  intro x hxA
  by_cases hA : (A : Set X).Nonempty
  · rcases hA with ⟨a, ha⟩
    have hAU : (A : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; trivial
      · intro _; 
        have : y = a := Subsingleton.elim y a
        simpa [this] using ha
    have : x ∈ (Set.univ : Set X) := by simp
    simpa [hAU, closure_univ, interior_univ] using this
  · cases hA ⟨x, hxA⟩