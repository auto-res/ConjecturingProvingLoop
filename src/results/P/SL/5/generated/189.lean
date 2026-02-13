

theorem interior_diff_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsClosed (B : Set X)) :
    interior (A \ B : Set X) = interior A \ B := by
  ext x
  constructor
  · intro hx
    have h := interior_diff_subset_interior_diff_closure
        (X := X) (A := A) (B := B) hx
    simpa [hB.closure_eq] using h
  · rintro ⟨hxIntA, hxNotB⟩
    -- `interior A` is open and contains `x`.
    rcases mem_interior.1 hxIntA with ⟨U, hUsubA, hUopen, hxU⟩
    -- The complement of the closed set `B` is open and contains `x`.
    have hOpenCompl : IsOpen ((Bᶜ : Set X)) := hB.isOpen_compl
    have hxComplB : x ∈ (Bᶜ : Set X) := by
      simpa using hxNotB
    -- The intersection `U ∩ Bᶜ` is an open neighborhood of `x`
    -- contained in `A \ B`.
    have hOpenInt : IsOpen (U ∩ (Bᶜ : Set X)) := hUopen.inter hOpenCompl
    have hxInt : x ∈ U ∩ (Bᶜ : Set X) := ⟨hxU, hxComplB⟩
    have hSub :
        (U ∩ (Bᶜ : Set X) : Set X) ⊆ A \ B := by
      intro y hy
      exact ⟨hUsubA hy.1, hy.2⟩
    exact mem_interior.2 ⟨U ∩ (Bᶜ : Set X), hSub, hOpenInt, hxInt⟩