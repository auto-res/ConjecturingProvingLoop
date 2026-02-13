

theorem P1_prod_right_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : P1 B) : P1 ((Set.univ : Set X) ×ˢ B) := by
  have h_univ : P1 (Set.univ : Set X) := P1_univ (X := X)
  simpa using
    (P1_prod (X := X) (Y := Y) (A := (Set.univ : Set X)) (B := B) h_univ hB)

theorem P2_iff_interior_dense {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ closure (interior A) = closure A ∧ A ⊆ interior (closure A) := by
  constructor
  · intro h2
    have hclosure : closure (interior (A : Set X)) = closure A :=
      dense_closure_of_P2 (A := A) h2
    have hsubset : (A : Set X) ⊆ interior (closure A) :=
      P3_of_P2 h2
    exact ⟨hclosure, hsubset⟩
  · rintro ⟨hclosure, hsubset⟩
    have h1 : P1 A :=
      (P1_iff_closure_interior_eq (A := A)).2 hclosure
    have h3 : P3 A := hsubset
    exact P2_of_P1_and_P3 h1 h3