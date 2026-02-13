

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  exact
    ⟨fun _ => P3_of_open (A := A) hA,
     fun _ => P1_of_open (X := X) (A := A) hA⟩

theorem exists_P3_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, U ⊆ A ∧ Topology.P3 U := by
  refine ⟨(∅ : Set X), Set.empty_subset _, ?_⟩
  simpa using (P3_empty (X := X))