

theorem exists_dense_interior_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, closure (interior A) = Set.univ ∧ Topology.P2 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simp
  · simpa using Topology.P2_univ (X := X)

theorem P2_iff_P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : Topology.P2 A ↔ Topology.P2 (e '' A) := by
  constructor
  · intro hA
    exact P2_image_homeomorph (e := e) (A := A) hA
  · intro hImg
    have h' : Topology.P2 ((e.symm) '' (e '' A)) :=
      P2_image_homeomorph (e := e.symm) (A := e '' A) hImg
    have hEq : ((e.symm) '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, rfl⟩
        rcases hy with ⟨z, hz, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, by
          simp⟩
    simpa [hEq] using h'

theorem exists_nonempty_open_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ Topology.P1 U := by
  classical
  obtain ⟨x⟩ := (‹Nonempty X›)
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_, ?_⟩
  · exact ⟨x, by simp⟩
  · simpa using Topology.P1_univ (X := X)