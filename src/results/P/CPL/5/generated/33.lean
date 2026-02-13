

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P1 A) : P1 (A ×ˢ (Set.univ : Set Y)) := by
  intro x hx
  rcases x with ⟨a, b⟩
  -- `a` is in `A`, hence in `closure (interior A)` by `hA`
  have ha : a ∈ closure (interior A) := hA hx.1
  -- `b` is trivially in the closure of the interior of `univ`
  have hb : b ∈ closure (interior (Set.univ : Set Y)) := by
    simpa [interior_univ, closure_univ] using (Set.mem_univ b)
  -- put the pieces together in the product
  have hprod :
      (a, b) ∈
        closure (interior A) ×ˢ
          closure (interior (Set.univ : Set Y)) := by
    exact ⟨ha, hb⟩
  -- rewrite the goal using the product rules for interior and closure
  simpa [closure_prod_eq, interior_prod_eq, interior_univ, closure_univ] using hprod