

theorem P1_iff_P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → closure A = Set.univ → (P1 A ↔ P2 A) := by
  intro hClosed hDense
  -- From closedness and density, deduce `A = univ`.
  have hA_univ : (A : Set X) = Set.univ := by
    have h_cl : closure A = A := hClosed.closure_eq
    simpa [h_cl] using hDense
  -- `P1` and `P2` both hold for `A` because `A = univ`.
  have hP1A : P1 A := by
    simpa [hA_univ] using (P1_univ (X := X))
  have hP2A : P2 A := by
    simpa [hA_univ] using (P2_univ (X := X))
  -- Conclude the equivalence.
  exact ⟨fun _ => hP2A, fun _ => hP1A⟩

theorem P1_iterate_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior (interior A)) := by
  intro x hx
  have h : x ∈ closure (interior (interior A)) := subset_closure hx
  simpa [interior_interior] using h

theorem P2_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 (interior (A ∪ B)) ↔ P2 (interior A ∪ interior B) := by
  have hOpen1 : IsOpen (interior (A ∪ B)) := isOpen_interior
  have hOpen2 : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union
      (isOpen_interior : IsOpen (interior B))
  have h1 := (P2_iff_P3_of_open (X := X) (A := interior (A ∪ B)) hOpen1)
  have h2 := (P3_interior_union (X := X) (A := A) (B := B))
  have h3 := (P2_iff_P3_of_open
                (X := X) (A := (interior A ∪ interior B)) hOpen2)
  simpa using h1.trans (h2.trans h3.symm)