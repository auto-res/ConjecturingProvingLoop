

theorem P2_subsingleton_iff {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 A ↔ True := by
  constructor
  · intro _h; trivial
  · intro _; exact P2_subsingleton (X := X) (A := A)

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) : Topology.P3 (A ∪ B ∪ C) := by
  -- Obtain `P3` for `A ∪ B`
  have hAB : Topology.P3 (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA hB
  -- Combine with `C`
  simpa [Set.union_assoc] using
    (Topology.P3_union (X := X) (A := A ∪ B) (B := C) hAB hC)

theorem exists_open_P3 {X : Type*} [TopologicalSpace X] : ∃ U : Set X, IsOpen U ∧ Topology.P3 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_⟩
  simpa using Topology.P3_univ (X := X)