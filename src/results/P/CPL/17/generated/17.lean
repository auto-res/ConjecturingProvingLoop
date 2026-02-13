

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_iff_P1_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A ↔ Topology.P1 A := by
  constructor
  · intro hP2
    exact P2_implies_P1 (A := A) hP2
  · intro _hP1
    exact P2_of_open (A := A) hA

theorem exists_dense_P1_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ B, A ⊆ B ∧ Dense B ∧ Topology.P1 B := by
  refine ⟨(Set.univ : Set X), Set.subset_univ _, dense_univ, P1_univ (X := X)⟩