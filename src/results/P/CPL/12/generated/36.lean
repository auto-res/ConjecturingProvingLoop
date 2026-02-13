

theorem P2_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A → P2 A := by
  intro hP3
  exact ((P2_iff_P3_of_closed (A := A) hA).mpr hP3)

theorem P3_of_P1_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A → P3 A := by
  intro _hP1
  exact P3_of_open (A := A) hA

theorem P1_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P1 (Aᶜ) := by
  intro hClosed
  exact P1_of_P2 (A := Aᶜ) (P2_of_closed_complement (A := A) hClosed)