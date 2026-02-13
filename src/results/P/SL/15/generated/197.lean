

theorem dense_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Dense (A ×ˢ B) ↔ (Dense A ∧ Dense B) := by
  constructor
  · intro hDenseProd
    -- `closure (A ×ˢ B)` is the whole space.
    have hClosureProd :
        (closure (A ×ˢ B) : Set (X × Y)) = (Set.univ : Set (X × Y)) := by
      simpa using hDenseProd.closure_eq
    -- Identify `closure (A ×ˢ B)` via the product rule.
    have hProdClosure :
        (closure (A ×ˢ B) : Set (X × Y)) = closure A ×ˢ closure B := by
      simpa using (closure_prod_eq (s := A) (t := B))
    -- Hence the product of closures is `univ`.
    have hProdUniv :
        closure A ×ˢ closure B = (Set.univ : Set (X × Y)) := by
      calc
        closure A ×ˢ closure B
            = (closure (A ×ˢ B) : Set (X × Y)) := by
                symm; simpa using hProdClosure
        _ = (Set.univ : Set (X × Y)) := hClosureProd
    -- Deduce `closure A = univ`.
    have hClosureA : (closure (A : Set X)) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro x _; trivial
      · intro x _
        rcases hBne with ⟨y0, _hy0⟩
        have : ((x, y0) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
          trivial
        have : ((x, y0) : X × Y) ∈ closure A ×ˢ closure B := by
          simpa [hProdUniv] using this
        exact (Set.mem_prod.1 this).1
    -- Deduce `closure B = univ`.
    have hClosureB : (closure (B : Set Y)) = (Set.univ : Set Y) := by
      apply Set.Subset.antisymm
      · intro y _; trivial
      · intro y _
        rcases hAne with ⟨x0, _hx0⟩
        have : ((x0, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
          trivial
        have : ((x0, y) : X × Y) ∈ closure A ×ˢ closure B := by
          simpa [hProdUniv] using this
        exact (Set.mem_prod.1 this).2
    -- Conclude density of the factors.
    have hDenseA : Dense A := (dense_iff_closure_eq).2 hClosureA
    have hDenseB : Dense B := (dense_iff_closure_eq).2 hClosureB
    exact ⟨hDenseA, hDenseB⟩
  · rintro ⟨hDenseA, hDenseB⟩
    exact dense_prod_of_dense_left_and_dense_right hDenseA hDenseB