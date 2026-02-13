

theorem exists_dense_P1_subset {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Dense A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), dense_univ, ?_⟩
  simpa using (P1_univ (X := X))

theorem P2_Union_closed {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (h : ∀ i, IsClosed (A i)) (hP : ∀ i, Topology.P2 (A i)) : Topology.P2 (⋃ i, A i) := by
  simpa using (P2_iUnion (X := X) (A := A) hP)

theorem P2_of_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} (hAc : IsClosed Aᶜ) : Topology.P2 A := by
  -- `A` is open since its complement is closed.
  have hA_open : IsOpen (A : Set X) := by
    simpa using hAc.isOpen_compl
  -- Apply the lemma giving `P2` for open sets.
  exact P2_of_open (A := A) hA_open

theorem exists_P3_between {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hA : Topology.P3 A) (hB : Topology.P3 B) : ∃ U, A ⊆ U ∧ U ⊆ B ∧ Topology.P3 U := by
  refine ⟨A ∪ interior B, ?_, ?_, ?_⟩
  · intro x hxA
    exact Or.inl hxA
  · intro x hxU
    cases hxU with
    | inl hxA => exact hAB hxA
    | inr hxIntB =>
        have hsubset : (interior B : Set X) ⊆ B := interior_subset
        exact hsubset hxIntB
  ·
    have hP3_intB : Topology.P3 (interior B) := by
      simpa using (P3_interior (X := X) (A := B))
    have hP3_union : Topology.P3 (A ∪ interior B) :=
      P3_union (X := X) (A := A) (B := interior B) hA hP3_intB
    simpa using hP3_union