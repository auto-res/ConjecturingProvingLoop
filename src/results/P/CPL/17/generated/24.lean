

theorem exists_open_P1_subset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ Topology.P1 U := by
  intro _hP1A
  exact
    ⟨interior A, isOpen_interior, interior_subset,
      P1_interior (X := X) (A := A)⟩

theorem P3_closed_union_dense {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsClosed A) (hB : Dense B) : Topology.P3 (A ∪ B) := by
  -- First, prove that the closure of `A ∪ B` is the whole space.
  have h_closure : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    -- Because `B` is dense, its closure is `univ`.
    have hB_closure : closure (B : Set X) = (Set.univ : Set X) := hB.closure_eq
    -- Since `B ⊆ A ∪ B`, we have `closure B ⊆ closure (A ∪ B)`.
    have h_subset : closure (B : Set X) ⊆ closure (A ∪ B) :=
      closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
    -- Thus `univ ⊆ closure (A ∪ B)`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure (A ∪ B) := by
      simpa [hB_closure] using h_subset
    -- The reverse inclusion is trivial.
    apply Set.Subset.antisymm
    · intro x _; trivial
    · exact h_univ_subset
  -- Apply the lemma that a set whose closure is `univ` satisfies `P3`.
  exact (P3_of_closure_eq_univ (A := A ∪ B)) h_closure