

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (A := interior A) := by
  apply Topology.P3_of_open
  simpa using isOpen_interior

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense (interior A)) : Topology.P3 (A := A) := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := by
    simpa [hA.closure_eq, interior_univ]
  have h_subset :
      interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono interior_subset
  exact h_subset hx'

theorem P3_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : Topology.P3 (A := A)) (hB : Topology.P3 (A := B)) (hC : Topology.P3 (A := C)) (hD : Topology.P3 (A := D)) : Topology.P3 (A := A ∪ B ∪ C ∪ D) := by
  -- First, combine `A`, `B`, and `C`
  have hABC : Topology.P3 (A := A ∪ B ∪ C) := by
    -- Combine `A` and `B`
    have hAB : Topology.P3 (A := A ∪ B) :=
      Topology.union_P3 (A := A) (B := B) hA hB
    -- Add `C`
    have hABC' : Topology.P3 (A := (A ∪ B) ∪ C) :=
      Topology.union_P3 (A := A ∪ B) (B := C) hAB hC
    simpa [Set.union_assoc] using hABC'
  -- Then add `D`
  simpa [Set.union_assoc] using
    Topology.union_P3 (A := A ∪ B ∪ C) (B := D) hABC hD

theorem P1_iff_P2_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X} (hA_open : IsOpen A) (hA_closed : IsClosed A) : Topology.P1 (A := A) ↔ Topology.P2 (A := A) := by
  have h1 : Topology.P1 (A := A) ↔ Topology.P3 (A := A) :=
    P1_iff_P3_of_clopen (A := A) hA_open hA_closed
  have h2 : Topology.P2 (A := A) ↔ Topology.P3 (A := A) :=
    (P2_iff_P3_of_open (A := A) hA_open)
  simpa using h1.trans h2.symm