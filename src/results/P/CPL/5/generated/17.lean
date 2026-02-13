

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P1 A) (hB : P1 B) : P1 (Set.image (fun x : X × Y => (x.1, x.2)) (A ×ˢ B)) := by
  intro x hx
  rcases hx with ⟨⟨a, b⟩, hmem, rfl⟩
  have ha : a ∈ closure (interior A) := hA hmem.1
  have hb : b ∈ closure (interior B) := hB hmem.2
  have hprod : (a, b) ∈ closure (interior A) ×ˢ closure (interior B) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P1 B → P1 (e.symm '' B) := by
  intro hB
  exact ((P1_image_homeomorph (e.symm) (A := B))).1 hB