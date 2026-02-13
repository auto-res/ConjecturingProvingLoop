

theorem P1_subsingleton_space {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : Topology.P1 A := by
  classical
  by_cases hAempty : (A : Set X) = ∅
  · -- Empty set case
    simpa [hAempty] using (P1_empty (X := X))
  · -- Non-empty case: in a subsingleton space this forces `A = univ`
    have hAuniv : (A : Set X) = (Set.univ : Set X) := by
      -- Pick an element of `A`
      obtain ⟨a, ha⟩ :=
        (Set.nonempty_iff_ne_empty).2 hAempty
      -- Show every element belongs to `A`
      ext x
      constructor
      · intro hx
        trivial
      · intro _
        -- All points are equal in a subsingleton space
        have : x = a := Subsingleton.elim _ _
        simpa [this] using ha
    -- Apply the `univ` lemma
    simpa [hAuniv] using (P1_univ (X := X))

theorem P2_iUnion_increasing {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (hmono : ∀ i j, s i ⊆ s j) (h : ∀ i, Topology.P2 (s i)) : Topology.P2 (⋃ i, s i) := by
  simpa using (P2_Union_family (X := X) (s := s) h)