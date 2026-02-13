

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (Set.image (fun x : X × Y => (x.1, x.2)) (A ×ˢ B)) := by
  intro x hx
  rcases hx with ⟨⟨a, b⟩, hmem, rfl⟩
  have ha : a ∈ interior (closure (interior A)) := hA hmem.1
  have hb : b ∈ interior (closure (interior B)) := hB hmem.2
  have hprod :
      (a, b) ∈
        interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) := by
    exact ⟨ha, hb⟩
  simpa [closure_prod_eq, interior_prod_eq] using hprod