

theorem P3_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior (closure A)) := by
  intro x hx
  have hsubset :
      interior (closure A) ⊆
        interior (closure (interior (closure A))) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  exact hsubset hx

theorem P3_union₃ {X : Type*} [TopologicalSpace X] {A B C : Set X} : P3 A → P3 B → P3 C → P3 (A ∪ B ∪ C) := by
  intro hP3A hP3B hP3C
  have hP3_AB : P3 (A ∪ B) := P3_union hP3A hP3B
  have hP3_ABC : P3 ((A ∪ B) ∪ C) := P3_union hP3_AB hP3C
  simpa [Set.union_assoc] using hP3_ABC

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  have hInt : interior A = A := hA.interior_eq
  constructor
  · intro hP2
    intro x hx
    simpa [hInt] using hP2 hx
  · intro hP3
    intro x hx
    simpa [hInt] using hP3 hx