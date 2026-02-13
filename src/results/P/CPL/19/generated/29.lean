

theorem P3_of_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P3 A := by
  classical
  by_cases hA : (A : Set X) = ∅
  · -- If `A` is empty, use the previously proved lemma.
    simpa [hA] using (P3_empty (X := X))
  · -- Otherwise, `A` is non-empty.
    have h_nonempty : (A : Set X).Nonempty :=
      Set.nonempty_iff_ne_empty.2 hA
    rcases h_nonempty with ⟨x₀, hx₀A⟩
    -- Show that `closure A = univ`.
    have h_closure_univ : closure A = (Set.univ : Set X) := by
      ext y
      constructor
      · intro _; simp
      · intro _
        -- In a subsingleton, every point equals `x₀`.
        have h_eq : y = x₀ := Subsingleton.elim y x₀
        have hx₀_cl : x₀ ∈ closure A := subset_closure hx₀A
        simpa [h_eq] using hx₀_cl
    -- Conclude using `P3_of_dense`.
    exact P3_of_dense (X := X) (A := A) h_closure_univ

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 A → P2 (Set.prod A (Set.univ : Set Y)) := by
  intro hP2A
  have hP2_univ : P2 (Set.univ : Set Y) := P2_univ (X := Y)
  simpa using
    (P2_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hP2A hP2_univ)