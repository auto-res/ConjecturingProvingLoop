

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P3 A → P3 (Set.prod A (Set.univ : Set Y)) := by
  intro hP3A
  have hP3_univ : P3 (Set.univ : Set Y) := P3_univ (X := Y)
  simpa using
    (P3_prod (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hP3A hP3_univ)

theorem P1_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P1 B → P1 (Set.prod (Set.univ : Set X) B) := by
  intro hP1B
  have hP1_univ : P1 (Set.univ : Set X) := P1_univ (X := X)
  simpa using
    (P1_prod
        (X := X) (Y := Y)
        (A := (Set.univ : Set X)) (B := B)
        hP1_univ hP1B)

theorem P2_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P2 B → P2 (Set.prod (Set.univ : Set X) B) := by
  intro hP2B
  have hP2_univ : P2 (Set.univ : Set X) := P2_univ (X := X)
  simpa using
    (P2_prod
        (X := X) (Y := Y)
        (A := (Set.univ : Set X)) (B := B)
        hP2_univ hP2B)

theorem P3_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P3 B → P3 (Set.prod (Set.univ : Set X) B) := by
  intro hP3B
  have hP3_univ : P3 (Set.univ : Set X) := P3_univ (X := X)
  simpa using
    (P3_prod
        (X := X) (Y := Y)
        (A := (Set.univ : Set X)) (B := B)
        hP3_univ hP3B)

theorem P3_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 (interior (A ∪ B)) ↔ P3 (interior A ∪ interior B) := by
  -- Both sets are open, hence automatically satisfy `P3`.
  have hOpen₁ : IsOpen (interior (A ∪ B)) := isOpen_interior
  have hOpen₂ : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union
      (isOpen_interior : IsOpen (interior B))
  have hP3₁ : P3 (interior (A ∪ B)) :=
    P3_of_open (X := X) (A := interior (A ∪ B)) hOpen₁
  have hP3₂ : P3 (interior A ∪ interior B) :=
    P3_of_open (X := X) (A := interior A ∪ interior B) hOpen₂
  exact ⟨fun _ => hP3₂, fun _ => hP3₁⟩