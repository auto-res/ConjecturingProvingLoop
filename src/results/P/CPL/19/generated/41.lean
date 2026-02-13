

theorem P2_iff_P1_and_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P1 A := by
  have hP2P3 : P2 A ↔ P3 A :=
    P2_iff_P3_of_open (X := X) (A := A) hA
  have hP1P3 : P1 A ↔ P3 A :=
    P1_iff_P3_of_open (X := X) (A := A) hA
  simpa using hP2P3.trans hP1P3.symm

theorem P2_Union_closed {X : Type*} [TopologicalSpace X] {F : ℕ → Set X} : (∀ n, IsClosed (F n)) → (∀ n, P2 (F n)) → P2 (⋃ n, F n) := by
  intro hClosed hP2
  -- touch `hClosed` to avoid an unused-argument warning
  have _ := hClosed 0
  simpa using (P2_iSup_family (X := X) (F := F) hP2)

theorem P2_prod_inf {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A₁ A₂ : Set X} {B₁ B₂ : Set Y} : P2 (A₁ ∩ A₂) → P2 (B₁ ∩ B₂) → P2 ((A₁ ∩ A₂) ×ˢ (B₁ ∩ B₂)) := by
  intro hP2A hP2B
  simpa using
    (P2_prod (X := X) (Y := Y)
      (A := A₁ ∩ A₂) (B := B₁ ∩ B₂) hP2A hP2B)