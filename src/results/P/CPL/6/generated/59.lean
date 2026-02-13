

theorem P2_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 (Aᶜ) := by
  intro hClosedA
  have hOpen : IsOpen (Aᶜ : Set X) := hClosedA.isOpen_compl
  have hP3 : P3 (Aᶜ : Set X) := P3_compl_of_closed (A := A) hClosedA
  exact (P3_iff_P2_of_open (A := Aᶜ) hOpen).1 hP3

theorem P2_union_open {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsOpen B) : P2 A → P2 (A ∪ B) := by
  intro hP2A
  have hP2B : P2 B := P2_of_open (A := B) hB
  exact P2_union (A := A) (B := B) hP2A hP2B