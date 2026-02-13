

theorem P3_iff_P2_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : Topology.P3 A ↔ Topology.P2 A := by
  -- From the density of `interior A` we obtain the equality of closures.
  have h_closure : (closure (interior (A : Set X)) : Set X) = Set.univ := by
    simpa using h.closure_eq
  -- This equality implies `P2 A`.
  have hP2_dense : Topology.P2 A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h_closure
  -- Establish the equivalence.
  exact
    ⟨fun _hP3 => hP2_dense,
     fun hP2 => Topology.P2_implies_P3 (X := X) (A := A) hP2⟩

theorem exists_dense_P1_open_closed {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsOpen A ∧ IsClosed A ∧ Dense A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), isOpen_univ, isClosed_univ, dense_univ, ?_⟩
  simpa using Topology.P1_univ (X := X)

theorem P2_prod_infinite {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Infinite X] [Infinite Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ×ˢ B) := by
  simpa using
    (Topology.P2_prod
        (X := X) (Y := Y)
        (A := A) (B := B)
        hA hB)