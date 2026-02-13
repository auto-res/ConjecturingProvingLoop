

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  intro x hx
  -- First inclusion: closure A ⊆ closure (interior A)
  have hsubset1 : (closure A : Set X) ⊆ closure (interior A) := by
    have : (closure A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hP1
    simpa [closure_closure] using this
  -- Second inclusion: closure (interior A) ⊆ closure (interior (closure A))
  have hsubset2 :
      (closure (interior A) : Set X) ⊆ closure (interior (closure A)) := by
    have : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono this
  exact hsubset2 (hsubset1 hx)

theorem P1_prod_set {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (A ×ˢ B) := by
  intro x hx
  rcases x with ⟨a, b⟩
  have ha : a ∈ closure (interior A) := hA hx.1
  have hb : b ∈ closure (interior B) := hB hx.2
  have hprod : (a, b) ∈ closure (interior A) ×ˢ closure (interior B) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod

theorem P2_prod_set {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (A ×ˢ B) := by
  intro x hx
  rcases x with ⟨a, b⟩
  rcases hx with ⟨haA, hbB⟩
  have ha : a ∈ interior (closure (interior A)) := hA haA
  have hb : b ∈ interior (closure (interior B)) := hB hbB
  have hprod :
      (a, b) ∈
        interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod

theorem P3_prod_set {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (A ×ˢ B) := by
  intro x hx
  rcases x with ⟨a, b⟩
  rcases hx with ⟨haA, hbB⟩
  have ha : a ∈ interior (closure A) := hA haA
  have hb : b ∈ interior (closure B) := hB hbB
  have hprod :
      (a, b) ∈ interior (closure A) ×ˢ interior (closure B) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod